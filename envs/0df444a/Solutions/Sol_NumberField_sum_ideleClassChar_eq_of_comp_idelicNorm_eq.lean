-- Prove2me | solution 1 for NumberField.sum_ideleClassChar_eq_of_comp_idelicNorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/70824190-f872-5f71-9d23-96fc7ff8bdc6

import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_isOpen_range_idelicNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_sum_ideleClassChar_eq_of_comp_idelicNorm_eq
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField

noncomputable section

namespace R2ChiCharEngine

def expQ : Multiplicative ℚ →* ℂˣ where
  toFun q := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * ((Multiplicative.toAdd q : ℚ) : ℂ)))
    (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp only [toAdd_mul, Rat.cast_add, Units.val_mk0, Units.val_mul]
    rw [← Complex.exp_add]
    congr 1
    ring

theorem expQ_apply (q : ℚ) :
    ((expQ (Multiplicative.ofAdd q) : ℂˣ) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) := rfl

theorem expQ_eq_one_iff (q : ℚ) : expQ (Multiplicative.ofAdd q) = 1 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    have h' : Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) = 1 := by
      rw [← expQ_apply, h, Units.val_one]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hq : (q : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ h2
      rw [hn, mul_comm]
    have hq' : ((q : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by rw [hq, Rat.cast_intCast]
    exact (Rat.cast_injective hq').symm
  · rintro ⟨n, rfl⟩
    ext
    rw [expQ_apply, Units.val_one]
    exact Complex.exp_eq_one_iff.mpr ⟨n, by push_cast; ring⟩

def expQadd : ℚ →+ Additive ℂˣ where
  toFun q := Additive.ofMul (expQ (Multiplicative.ofAdd q))
  map_zero' := by rw [ofAdd_zero, map_one, ofMul_one]
  map_add' a b := by rw [ofAdd_add, map_mul, ofMul_mul]

def jHom : AddCircle (1 : ℚ) →+ Additive ℂˣ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) expQadd (by
    intro x hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [AddMonoidHom.mem_ker]
    show Additive.ofMul (expQ (Multiplicative.ofAdd (k • (1 : ℚ)))) = 0
    rw [ofMul_eq_zero, expQ_eq_one_iff]
    exact ⟨k, by simp⟩)

theorem jHom_mk (q : ℚ) :
    jHom (QuotientAddGroup.mk q) = Additive.ofMul (expQ (Multiplicative.ofAdd q)) :=
  QuotientAddGroup.lift_mk _ _ q

theorem jHom_injective : Function.Injective jHom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    rw [jHom_mk, ofMul_eq_zero, expQ_eq_one_iff] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp⟩

theorem exists_char_apply_ne_one {A : Type*} [CommGroup A] {a : A} (ha : a ≠ 1) :
    ∃ ψ : A →* ℂˣ, ψ a ≠ 1 := by
  have ha' : (Additive.ofMul a : Additive A) ≠ 0 := by rwa [Ne, ofMul_eq_zero]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha'

  let ψadd : Additive A →+ Additive ℂˣ := jHom.comp c
  refine ⟨MonoidHom.toAdditive.symm ψadd, ?_⟩
  intro h1
  apply hc
  apply jHom_injective
  rw [map_zero]
  have h2 : ψadd (Additive.ofMul a) = 0 := by
    have h2 := congrArg Additive.ofMul h1
    rw [ofMul_one] at h2
    exact h2
  exact h2

section Duality

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_of_ker_le {H : Subgroup G} (hH : IsOpen (H : Set G)) (χ : G →* ℂˣ)
    (hχ : H ≤ χ.ker) : Continuous fun z => ((χ z : ℂˣ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hopen : IsOpen ((fun z => g⁻¹ * z) ⁻¹' (H : Set G)) := hH.preimage (continuous_const_mul g⁻¹)
  have hmem : g ∈ (fun z => g⁻¹ * z) ⁻¹' (H : Set G) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact H.one_mem
  refine (continuousAt_const : ContinuousAt (fun _ : G => ((χ g : ℂˣ) : ℂ)) g).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with z hz
  have h1 : χ (g⁻¹ * z) = 1 := hχ hz
  have hz' : χ z = χ g := by
    rw [← mul_inv_cancel_left g z, map_mul, h1, mul_one]
  rw [hz']

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem ker_le_mul {H : Subgroup G} {χ₁ χ : G →* ℂˣ} (h₁ : H ≤ χ₁.ker) (h : H ≤ χ.ker) :
    H ≤ (χ₁ * χ).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, show χ₁ x = 1 from h₁ hx, show χ x = 1 from h hx,
    one_mul]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem card_eq_index_and_sum_eq_zero (H : Subgroup G) (X : Finset (G →* ℂˣ))
    (hX : ∀ χ : G →* ℂˣ, χ ∈ X ↔ H ≤ χ.ker) :
    X.card = H.index ∧ ∀ g : G, g ∉ H → ∑ χ ∈ X, ((χ g : ℂˣ) : ℂ) = 0 := by
  classical

  let Q := G ⧸ H
  let e : {χ // χ ∈ X} ≃ (Q →* ℂˣ) :=
    { toFun := fun χ => QuotientGroup.lift H χ.1 ((hX _).1 χ.2)
      invFun := fun ψ => ⟨ψ.comp (QuotientGroup.mk' H), (hX _).2 (by
        intro h hh
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          (QuotientGroup.eq_one_iff h).mpr hh, map_one])⟩
      left_inv := fun χ => by
        apply Subtype.ext
        ext g
        rfl
      right_inv := fun ψ => by
        ext q
        rfl }
  haveI : Fintype (Q →* ℂˣ) := Fintype.ofEquiv _ e

  set m : ℕ := Fintype.card (Q →* ℂˣ) with hm
  have hmpos : 0 < m := Fintype.card_pos
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have hpow : ∀ (ψ : Q →* ℂˣ) (q : Q), ψ q ^ m = 1 := fun ψ q => by
    rw [← MonoidHom.pow_apply, hm, pow_card_eq_one, MonoidHom.one_apply]
  let f : Q → ((Q →* ℂˣ) → rootsOfUnity m ℂ) := fun q ψ => ⟨ψ q, (mem_rootsOfUnity _ _).mpr (hpow ψ q)⟩
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    by_contra hne
    have hne' : q₁ * q₂⁻¹ ≠ 1 := by rwa [Ne, mul_inv_eq_one]
    obtain ⟨ψ, hψ⟩ := exists_char_apply_ne_one hne'
    apply hψ
    have := congrArg (fun F => ((F ψ : rootsOfUnity m ℂ) : ℂˣ)) h
    simp only [f] at this
    rw [map_mul, map_inv, this, mul_inv_cancel]
  haveI : Finite Q := Finite.of_injective f hf
  refine ⟨?_, ?_⟩
  ·
    haveI : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    have h1 : X.card = Fintype.card (Q →* ℂˣ) := by
      rw [← Fintype.card_coe, Fintype.card_congr e]
    rw [h1, Fintype.card_eq_nat_card, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ,
      Subgroup.index_eq_card]
  ·
    intro g hg
    have hg' : (QuotientGroup.mk g : Q) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
    obtain ⟨ψ₁, hψ₁⟩ := exists_char_apply_ne_one hg'
    let χ₁ : G →* ℂˣ := ψ₁.comp (QuotientGroup.mk' H)
    have hχ₁ : H ≤ χ₁.ker := (hX _).1 (e.symm ψ₁).2
    have hχ₁g : χ₁ g ≠ 1 := hψ₁
    set S := ∑ χ ∈ X, ((χ g : ℂˣ) : ℂ) with hS
    have hshift : S = ((χ₁ g : ℂˣ) : ℂ) * S := by
      rw [hS, Finset.mul_sum]
      symm
      refine Finset.sum_nbij' (fun χ => χ₁ * χ) (fun χ => χ₁⁻¹ * χ) ?_ ?_ ?_ ?_ ?_
      · intro χ hχ
        exact (hX _).2 (ker_le_mul hχ₁ ((hX _).1 hχ))
      · intro χ hχ
        refine (hX _).2 (ker_le_mul ?_ ((hX _).1 hχ))
        intro x hx
        rw [MonoidHom.mem_ker, MonoidHom.inv_apply, show χ₁ x = 1 from hχ₁ hx, inv_one]
      · intro χ _
        exact inv_mul_cancel_left χ₁ χ
      · intro χ _
        exact mul_inv_cancel_left χ₁ χ
      · intro χ _
        rw [MonoidHom.mul_apply, Units.val_mul]
    have hne : ((χ₁ g : ℂˣ) : ℂ) ≠ 1 := by
      intro h
      exact hχ₁g (Units.val_eq_one.mp h)
    have : (((χ₁ g : ℂˣ) : ℂ) - 1) * S = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h

end Duality

end R2ChiCharEngine

end

open R2ChiCharEngine in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩)) :
    (∀ (a : Kˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ∑ ξ ∈ Ξ, ((ξ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a *
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
        (Ξ.card : ℂ) * ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
    (∀ u : (AdeleRing (𝓞 K) K)ˣ,
      u ∉ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range →
        ∑ ξ ∈ Ξ, ((ξ ⟨u, Subgroup.mem_top u⟩ : ℂˣ) : ℂ) = 0) ∧
    (Ξ.Nonempty → Ξ.card =
      ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊔
        (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range).index) := by
  classical

  set ι : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) with hι
  set N : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hN
  set H : Subgroup (AdeleRing (𝓞 K) K)ˣ := ι.range ⊔ N.range with hH

  let toG : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :=
    fun ξ => ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ≃* _).symm.toMonoidHom
  have toG_apply : ∀ (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      toG ξ z = ξ ⟨z, Subgroup.mem_top z⟩ := fun _ _ => rfl
  let ofG : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :=
    fun χ => χ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ≃* _).toMonoidHom
  have toG_ofG : ∀ χ, toG (ofG χ) = χ := fun χ => by
    ext z
    rfl
  have ofG_toG : ∀ ξ, ofG (toG ξ) = ξ := fun ξ => by
    ext z
    rfl
  have toG_inj : Function.Injective toG := fun ξ₁ ξ₂ h => by
    rw [← ofG_toG ξ₁, ← ofG_toG ξ₂, h]

  refine ⟨?_, ?_⟩
  · intro a z
    have key : ∀ ξ ∈ Ξ, ((ξ ⟨ι a * N z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      intro ξ hξ
      obtain ⟨-, htriv, hnorm⟩ := (hΞ ξ).1 hξ
      have hmul : (⟨ι a * N z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
          ⟨ι a, Subgroup.mem_top _⟩ * ⟨N z, Subgroup.mem_top _⟩ := rfl
      rw [hmul, map_mul, htriv (ι a) ⟨a, rfl⟩, one_mul, hnorm z]
    rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul]

  rcases Ξ.eq_empty_or_nonempty with hempty | ⟨ξ₀, hξ₀⟩
  · subst hempty
    exact ⟨fun u _ => by simp, fun h => absurd h Finset.not_nonempty_empty⟩
  obtain ⟨hc₀, ht₀, hn₀⟩ := (hΞ ξ₀).1 hξ₀
  set φ₀ := toG ξ₀ with hφ₀

  have hHopen : IsOpen (H : Set (AdeleRing (𝓞 K) K)ˣ) :=
    Subgroup.isOpen_mono le_sup_right
      (NumberField.isOpen_range_idelicNorm K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L))

  let X : Finset ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := Ξ.image fun ξ => toG ξ / φ₀
  have hX : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, χ ∈ X ↔ H ≤ χ.ker := by
    intro χ
    constructor
    · intro hχ
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hχ
      obtain ⟨-, ht, hn⟩ := (hΞ ξ).1 hξ
      intro h hh
      rw [hH] at hh
      obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup.mp hh
      obtain ⟨t, rfl⟩ := hw
      rw [MonoidHom.mem_ker, map_mul, MonoidHom.div_apply, MonoidHom.div_apply, toG_apply, toG_apply,
        hφ₀, toG_apply, toG_apply, ht y hy, ht₀ y hy, hn t, hn₀ t, div_one, div_self', one_mul]
    · intro hker
      have hcont : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ * φ₀) z : ℂˣ) : ℂ) := by
        have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ * φ₀) z : ℂˣ) : ℂ)) =
            fun z => ((χ z : ℂˣ) : ℂ) * ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
          funext z
          rw [MonoidHom.mul_apply, Units.val_mul, hφ₀, toG_apply]
        rw [this]
        exact (continuous_of_ker_le hHopen χ hker).mul hc₀
      have hmem : ofG (χ * φ₀) ∈ Ξ := by
        refine (hΞ _).2 ⟨?_, ?_, ?_⟩
        · have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ofG (χ * φ₀) ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) =
              fun z => (((χ * φ₀) z : ℂˣ) : ℂ) := by
            funext z
            rw [← toG_apply, toG_ofG]
          rw [this]
          exact hcont
        · intro z hz
          rw [← toG_apply, toG_ofG, MonoidHom.mul_apply, hφ₀, toG_apply, ht₀ z hz, mul_one]
          exact hker (le_sup_left (a := ι.range) (b := N.range) hz)
        · intro z
          rw [← toG_apply, toG_ofG, MonoidHom.mul_apply, hφ₀, toG_apply, hn₀ z]
          have : χ (N z) = 1 := hker (le_sup_right (a := ι.range) (b := N.range) ⟨z, rfl⟩)
          rw [this, one_mul]
      refine Finset.mem_image.mpr ⟨ofG (χ * φ₀), hmem, ?_⟩
      rw [toG_ofG]
      exact mul_div_cancel_right χ φ₀
  obtain ⟨hcard, horth⟩ := card_eq_index_and_sum_eq_zero H X hX
  have hinj : Function.Injective fun ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ => toG ξ / φ₀ :=
    fun ξ₁ ξ₂ h => toG_inj (MonoidHom.ext fun z => by
      have hz := DFunLike.congr_fun h z
      simp only [MonoidHom.div_apply] at hz
      exact div_left_injective hz)
  have hXcard : X.card = Ξ.card := Finset.card_image_of_injective _ hinj
  refine ⟨?_, fun _ => by rw [← hXcard, hcard]⟩
  intro u hu
  have hsum : ∑ ξ ∈ Ξ, ((ξ ⟨u, Subgroup.mem_top u⟩ : ℂˣ) : ℂ) =
      ((φ₀ u : ℂˣ) : ℂ) * ∑ χ ∈ X, ((χ u : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum, Finset.sum_image fun ξ₁ _ ξ₂ _ h => hinj h]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [MonoidHom.div_apply, Units.val_div_eq_div_val, mul_div_cancel₀ _ (Units.ne_zero (φ₀ u))]
    rfl
  rw [hsum, horth u hu, mul_zero]

end S_NumberField_sum_ideleClassChar_eq_of_comp_idelicNorm_eq
end P2MW
export P2MW.S_NumberField_sum_ideleClassChar_eq_of_comp_idelicNorm_eq (solution)
