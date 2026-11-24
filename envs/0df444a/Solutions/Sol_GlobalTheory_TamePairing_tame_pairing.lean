-- Prove2me | solution 1 for GlobalTheory.TamePairing.tame_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:39.54317+00:00
-- url     : https://prove2.me/submissions/aeb6706f-42aa-4e56-9f26-4b856df36505

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TamePairing
import Theorems.Thm_GlobalTheory_TamePairing_exists_apply_eq_pow_mul
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_GlobalTheory_Published_TameSymbol_of_equiv
import Theorems.Thm_GlobalTheory_TameQuot_coe_mem_ineKer
import Theorems.Thm_GlobalTheory_TameQuot_cupMu_mk
import Theorems.Thm_GlobalTheory_TameQuot_exists_isUnifRoot
import Theorems.Thm_GlobalTheory_TameQuot_ineKer_le_Ine
import Theorems.Thm_GlobalTheory_TameQuot_mem_proKer
import Theorems.Thm_ReciprocityTheory_Gal_Ine_le_Dec
import Theorems.Thm_ReciprocityTheory_Gal_isOpen_setOf_apply
import Theorems.Thm_ReciprocityTheory_Gal_mem_Z1_iff_cocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
namespace GlobalTheory.TamePairing
open GlobalTheory.TameQuot
open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem ne_zero_of_isUnifRoot {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} [NeZero N] {x : Ω}
    (hx : _root_.GlobalTheory.TameQuot.IsUnifRoot v N x) : x ≠ 0 := by
  obtain ⟨ϖ, -, hϖ2, hxN⟩ := hx
  have hϖ : (ϖ : F) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]
    exact Submodule.zero_mem _
  rintro rfl
  rw [zero_pow (NeZero.ne N), eq_comm] at hxN
  exact hϖ ((map_eq_zero_iff _ (algebraMap F Ω).injective).1 hxN)
open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem apply_eq_self_of_cycMod_eq_one_of_pow_eq_one {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {g : _root_.Formalism.ConjugateSelfDual.G F Ω}
    (hg : _root_.ReciprocityTheory.Gal.cycMod F Ω l 1 g = 1) {t : Ω} (ht : t ^ l ^ 1 = 1) : g t = t := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h := cyclotomicCharacter.spec (L := Ω) l (n := 1) (MulSemiringAction.toRingAut _ Ω g) t ht
  have h1 : PadicInt.toZModPow 1
      ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut _ Ω g) : ℤ_[l])) = 1 :=
    congrArg Units.val hg
  rw [h1, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt (Nat.one_lt_pow one_ne_zero (Fact.out : l.Prime).one_lt), pow_one] at h
  exact h
open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem eq_of_primitiveRoot_pow_val_mul_eq {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ x : Ω}
    (hζ : IsPrimitiveRoot ζ N) (hx : x ≠ 0) {a b : ZMod N}
    (h : ζ ^ a.val * x = ζ ^ b.val * x) : a = b :=
  ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) (mul_right_cancel₀ hx h))
open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem primitiveRoot_pow_val_add_eq_mul {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow,
    mul_one]
open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem map_eq_one_of_mem_ine_kernel {F Ω : Type} [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {l : ℕ} [hl : Fact l.Prime] {m : ℕ}
    (ψ : _root_.ReciprocityTheory.Gal.Ine (F := F) A →* Multiplicative (ZMod (l ^ m)))
    (hψ : IsOpen (ψ.ker : Set (_root_.ReciprocityTheory.Gal.Ine (F := F) A))) {σ : _root_.ReciprocityTheory.Gal.Ine (F := F) A}
    (hσ : (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ _root_.GlobalTheory.TameQuot.ineKer F A l) : ψ σ = 1 := by
  rw [_root_.GlobalTheory.TameQuot.coe_mem_ineKer, _root_.GlobalTheory.TameQuot.mem_proKer] at hσ
  refine hσ ψ.ker inferInstance hψ ?_
  have hdvd : Nat.card ψ.range ∣ l ^ m := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod (l ^ m))), Fintype.card_multiplicative,
      ZMod.card] at this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl.out).1 hdvd
  exact ⟨i, by rw [Subgroup.index_ker, hi]⟩
open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem isClosed_setOf_pred_map_apply_of_isOpen_ker {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    [Algebra.IsIntegral F Ω] {H : Type} [Group H] (d : _root_.Formalism.ConjugateSelfDual.G F Ω →* H)
    (hd : IsOpen (d.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω))) (x : Ω) (P : H → Ω → Prop) :
    IsClosed {τ : _root_.Formalism.ConjugateSelfDual.G F Ω | P (d τ) (τ x)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro τ hτ
  refine ⟨(τ • (d.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω))) ∩ {σ | σ x = τ x}, ?_,
    (hd.leftCoset τ).inter (_root_.ReciprocityTheory.Gal.isOpen_setOf_apply x (· = τ x)), ?_, rfl⟩
  · rintro σ ⟨hσ, hσx⟩ hPσ
    rw [mem_leftCoset_iff, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
      inv_mul_eq_one] at hσ
    apply hτ
    simp only [Set.mem_setOf_eq] at hσx hPσ ⊢
    rw [hσ, ← hσx]
    exact hPσ
  · rw [mem_leftCoset_iff, inv_mul_cancel]
    exact one_mem _
end GlobalTheory.TamePairing
end

set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.TamePairing
open GlobalTheory.TameQuot
open NumberField IsDedekindDomain
open scoped Pointwise
namespace GlobalTheory.TamePairing
namespace _root_.GlobalTheory.TamePairing
theorem _root_.solution : _root_.GlobalTheory.Published.TameLocal → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → _root_.Formalism.ConjugateSelfDual.normV v ≡ 1 [MOD l ^ 1] → (∀ g : _root_.ReciprocityTheory.Gal.Dec (F := F) A, _root_.ReciprocityTheory.Gal.cycMod F Ω l 1 g = 1) → ∀ e : _root_.ReciprocityTheory.Gal.H2 (_root_.GlobalTheory.Published.PoitouTate.muLoc F l 1 A) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1), Function.Bijective e → ∀ (M : ℕ), 1 ≤ M → ∀ d : _root_.Formalism.ConjugateSelfDual.G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) → ∀ γ φ : _root_.ReciprocityTheory.Gal.Dec (F := F) A, (γ : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) (φ : _root_.Formalism.ConjugateSelfDual.G F Ω) → ∃ u : (ZMod (l ^ 1))ˣ, ∀ z y : _root_.ReciprocityTheory.Gal.Dec (F := F) A → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g : _root_.ReciprocityTheory.Gal.Dec (F := F) A, (g : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A → y g = 0) → ∀ w : _root_.ReciprocityTheory.Gal.Z2 (_root_.GlobalTheory.Published.PoitouTate.muLoc F l 1 A), (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = (u : ZMod (l ^ 1)) * (z γ * y φ) := by
  intro TL F Ω _ _ _ _ _ l _ A v hA hl hnorm hcyc e he M hM d hd γ φ hγ hdγ hφ
  obtain ⟨hS, hT⟩ := TL
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsIntegral F Ω := inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.TameQuot.exists_isUnifRoot (Ω := Ω) v (N := l ^ 1) (NeZero.pos _)
  have hx0 := ne_zero_of_isUnifRoot hx
  have hζfix : ∀ g : _root_.ReciprocityTheory.Gal.Dec (F := F) A, (g : _root_.Formalism.ConjugateSelfDual.G F Ω) ζ = ζ := fun g =>
    apply_eq_self_of_cycMod_eq_one_of_pow_eq_one (hcyc g) hζ.pow_eq_one
  choose χ0 hχ0 using fun g : _root_.ReciprocityTheory.Gal.Dec (F := F) A => _root_.GlobalTheory.TamePairing.exists_apply_eq_pow_mul hζ hx (g : _root_.Formalism.ConjugateSelfDual.G F Ω)
  have hχuniq : ∀ (g : _root_.ReciprocityTheory.Gal.Dec (F := F) A) (m : ZMod (l ^ 1)), (g : _root_.Formalism.ConjugateSelfDual.G F Ω) x = ζ ^ m.val * x → χ0 g = m :=
    fun g m h => eq_of_primitiveRoot_pow_val_mul_eq hζ hx0 ((hχ0 g).symm.trans h)
  let χ : _root_.ReciprocityTheory.Gal.Dec (F := F) A →* Multiplicative (ZMod (l ^ 1)) :=
    { toFun := fun g => Multiplicative.ofAdd (χ0 g)
      map_one' := by
        show Multiplicative.ofAdd (χ0 1) = Multiplicative.ofAdd 0
        rw [hχuniq 1 0 (by simp)]
      map_mul' := by
        intro g h
        show Multiplicative.ofAdd (χ0 (g * h)) = Multiplicative.ofAdd (χ0 g + χ0 h)
        rw [hχuniq (g * h) (χ0 g + χ0 h)]
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hχ0 h, map_mul, map_pow, hζfix g, hχ0 g,
          primitiveRoot_pow_val_add_eq_mul hζ]
        ring }

  obtain ⟨-, -, -, -, ⟨γ0, hγ0⟩, -⟩ := hS F Ω l A v hA hl
  let γ0' : _root_.ReciprocityTheory.Gal.Dec (F := F) A := ⟨γ0, _root_.ReciprocityTheory.Gal.Ine_le_Dec A hγ0.1⟩
  have hc0 : IsUnit (χ0 γ0') :=
    ((hT F Ω l 1 A v hA hl hnorm ζ hζ).2 x hx γ0' (χ0 γ0') hγ0.1 (hχ0 γ0')).1 hγ0
  have hKd : ∀ σ : _root_.Formalism.ConjugateSelfDual.G F Ω, σ ∈ _root_.GlobalTheory.TameQuot.ineKer F A l → d σ = 1 := by
    intro σ hσ
    exact map_eq_one_of_mem_ine_kernel (σ := ⟨σ, _root_.GlobalTheory.TameQuot.ineKer_le_Ine A l hσ⟩)
      (d.comp (_root_.ReciprocityTheory.Gal.Ine (F := F) A).subtype) (hd.preimage continuous_subtype_val) hσ
  have hkerχ : ((χ.comp (Subgroup.inclusion (_root_.ReciprocityTheory.Gal.Ine_le_Dec (F := F) A))).ker : Set (_root_.ReciprocityTheory.Gal.Ine (F := F) A)) =
      Subtype.val ⁻¹' {τ : _root_.Formalism.ConjugateSelfDual.G F Ω | τ x = x} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, Set.mem_preimage,
      Set.mem_setOf_eq]
    show Multiplicative.ofAdd (χ0 _) = Multiplicative.ofAdd 0 ↔ _
    rw [EmbeddingLike.apply_eq_iff_eq]
    constructor
    · intro h
      have := hχ0 (Subgroup.inclusion (_root_.ReciprocityTheory.Gal.Ine_le_Dec (F := F) A) σ)
      rw [h] at this
      simpa using this
    · intro h
      exact hχuniq _ 0 (by simpa using h)
  have hKχ : ∀ σ : _root_.Formalism.ConjugateSelfDual.G F Ω, σ ∈ _root_.GlobalTheory.TameQuot.ineKer F A l → σ x = x := by
    intro σ hσ
    have hσI := _root_.GlobalTheory.TameQuot.ineKer_le_Ine A l hσ
    have h1 := map_eq_one_of_mem_ine_kernel (σ := ⟨σ, hσI⟩)
      (χ.comp (Subgroup.inclusion (_root_.ReciprocityTheory.Gal.Ine_le_Dec (F := F) A)))
      (by rw [hkerχ]; exact (_root_.ReciprocityTheory.Gal.isOpen_setOf_apply x (· = x)).preimage continuous_subtype_val) hσ
    have hmem : (⟨σ, hσI⟩ : _root_.ReciprocityTheory.Gal.Ine (F := F) A) ∈ (χ.comp (Subgroup.inclusion (_root_.ReciprocityTheory.Gal.Ine_le_Dec (F := F) A))).ker := h1
    rw [← SetLike.mem_coe, hkerχ] at hmem
    exact hmem
  have hγcl : (γ : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ closure ((Subgroup.zpowers γ0 ⊔ _root_.GlobalTheory.TameQuot.ineKer F A l :
      Subgroup (_root_.Formalism.ConjugateSelfDual.G F Ω)) : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hγ0.2 hγ
  let Φ : Multiplicative (ZMod (l ^ M)) →* Multiplicative (ZMod (l ^ 1)) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom (pow_dvd_pow l hM) (ZMod (l ^ 1))).toAddMonoidHom
  have hΦK : ∀ σ : _root_.Formalism.ConjugateSelfDual.G F Ω, σ ∈ _root_.GlobalTheory.TameQuot.ineKer F A l → Φ (d σ) = 1 := by
    intro σ hσ
    rw [hKd σ hσ, map_one]
  have hΦγ : Φ (d γ) = Multiplicative.ofAdd 1 := by
    rw [hdγ]
    show Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow l hM) (ZMod (l ^ 1)) 1) = _
    rw [map_one]
  have ha : Φ (d γ0) ≠ 1 := by
    intro ha
    have hle : ((Subgroup.zpowers γ0 ⊔ _root_.GlobalTheory.TameQuot.ineKer F A l : Subgroup (_root_.Formalism.ConjugateSelfDual.G F Ω)) :
        Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) ⊆ {τ | Φ (d τ) = 1} := by
      have : Subgroup.zpowers γ0 ⊔ _root_.GlobalTheory.TameQuot.ineKer F A l ≤ (Φ.comp d).ker :=
        sup_le (Subgroup.zpowers_le.2 ha) (fun σ hσ => hΦK σ hσ)
      exact this
    have hW := closure_minimal hle (isClosed_setOf_pred_map_apply_of_isOpen_ker d hd x (fun h _ => Φ h = 1)) hγcl
    simp only [Set.mem_setOf_eq, hΦγ] at hW
    exact one_ne_zero (Multiplicative.ofAdd.injective (hW.trans ofAdd_zero.symm))

  set k : ZMod (l ^ 1) := χ0 γ0' * (Multiplicative.toAdd (Φ (d γ0)))⁻¹ with hk
  have ha' : Multiplicative.toAdd (Φ (d γ0)) ≠ 0 := fun h => ha (by rw [← ofAdd_toAdd (Φ (d γ0)), h, ofAdd_zero])
  let f : _root_.ReciprocityTheory.Gal.Dec (F := F) A →* Multiplicative (ZMod (l ^ 1)) :=
    (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft k)).comp (Φ.comp (d.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype))
  have hf : ∀ g : _root_.ReciprocityTheory.Gal.Dec (F := F) A, f g = Multiplicative.ofAdd (k * Multiplicative.toAdd (Φ (d g))) :=
    fun g => rfl
  have hle : ((Subgroup.zpowers γ0 ⊔ _root_.GlobalTheory.TameQuot.ineKer F A l : Subgroup (_root_.Formalism.ConjugateSelfDual.G F Ω)) :
      Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) ⊆ {τ | τ x = ζ ^ (k * Multiplicative.toAdd (Φ (d τ))).val * x} := by
    have h1 : Subgroup.zpowers γ0 ⊔ _root_.GlobalTheory.TameQuot.ineKer F A l ≤
        (MonoidHom.eqLocus χ f).map (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype := by
      refine sup_le (Subgroup.zpowers_le.2 ⟨γ0', ?_, rfl⟩) (fun σ hσ => ⟨⟨σ, _root_.ReciprocityTheory.Gal.Ine_le_Dec A
        (_root_.GlobalTheory.TameQuot.ineKer_le_Ine A l hσ)⟩, ?_, rfl⟩)
      · show Multiplicative.ofAdd (χ0 γ0') = f γ0'
        rw [hf, hk, mul_assoc, inv_mul_cancel₀ ha', mul_one]
      · show Multiplicative.ofAdd (χ0 _) = f _
        rw [hf, hχuniq _ 0 (by simpa using hKχ σ hσ)]
        show Multiplicative.ofAdd 0 = Multiplicative.ofAdd (k * Multiplicative.toAdd (Φ (d σ)))
        rw [hΦK σ hσ, toAdd_one, mul_zero]
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := h1 hτ
    have hσ' : χ0 σ = k * Multiplicative.toAdd (Φ (d σ)) := Multiplicative.ofAdd.injective hσ
    show (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) x = _
    rw [hχ0 σ, hσ']
    rfl
  have hZ := closure_minimal hle (isClosed_setOf_pred_map_apply_of_isOpen_ker d hd x
    (fun h y => y = ζ ^ (k * Multiplicative.toAdd (Φ h)).val * x)) hγcl
  simp only [Set.mem_setOf_eq, hΦγ, toAdd_ofAdd, mul_one] at hZ
  have hcγ : χ0 γ = k := hχuniq γ k hZ
  have hcU : IsUnit (χ0 γ) := by
    rw [hcγ]
    exact hc0.mul (isUnit_iff_ne_zero.2 (inv_ne_zero ha'))

  obtain ⟨u0, hu0⟩ := hT.of_equiv hA hl hnorm hζ (LinearEquiv.ofBijective e he)
  refine ⟨hcU.unit⁻¹ * u0, ?_⟩
  intro z y hz hy hzadd hyadd hyI w hw
  have hρ : ∀ (g : _root_.ReciprocityTheory.Gal.Dec (F := F) A) (m : ZMod (l ^ 1)),
      _root_.GlobalTheory.TameQuot.muDec F A l 1 g m = m := by
    intro g m
    unfold _root_.GlobalTheory.TameQuot.muDec
    rw [_root_.ReciprocityTheory.Gal.charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hcyc g, Units.val_one, one_mul]
  let zc : _root_.ReciprocityTheory.Gal.Z1 (_root_.GlobalTheory.TameQuot.trivDec F A l 1) :=
    ⟨z, (_root_.ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ z).2 ⟨hz, fun g h => by
      rw [hzadd]
      unfold _root_.GlobalTheory.TameQuot.trivDec
      simp⟩⟩
  let yc : _root_.ReciprocityTheory.Gal.Z1 (_root_.GlobalTheory.TameQuot.muDec F A l 1) :=
    ⟨y, (_root_.ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ y).2 ⟨hy, fun g h => by rw [hyadd, hρ]⟩⟩
  have hcup := _root_.GlobalTheory.TameQuot.cupMu_mk zc yc w (fun g h => by
    rw [hw, hρ])
  have hyH : Submodule.Quotient.mk yc ∈ _root_.ReciprocityTheory.Gal.H1ur (_root_.GlobalTheory.TameQuot.muDec F A l 1)
      ((_root_.ReciprocityTheory.Gal.Ine (F := F) A).subgroupOf (_root_.ReciprocityTheory.Gal.Dec (F := F) A)) := by
    unfold _root_.ReciprocityTheory.Gal.H1ur
    rw [LinearMap.mem_ker]
    unfold _root_.ReciprocityTheory.Gal.resH1
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    convert Submodule.zero_mem _
    apply Subtype.ext
    funext g
    exact hyI _ g.2
  have key := hu0 x hx γ (χ0 γ) hγ (hχ0 γ) φ hφ zc yc hyH
  rw [hcup] at key
  change χ0 γ * e (Submodule.Quotient.mk w) = (u0 : ZMod (l ^ 1)) * (z γ * y φ) at key
  rw [Units.val_mul, mul_assoc, ← key, ← mul_assoc, hcU.val_inv_mul, one_mul]
end _root_.GlobalTheory.TamePairing
end GlobalTheory.TamePairing
