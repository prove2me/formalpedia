-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_smoothPointStalk_of_affineChart_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d47e6e6c-0eec-582d-9973-eec41b7f7e08

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_Algebra_FormallySmooth_exists_etaleCoordinate_of_krullDimLE_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointStalk_of_affineChart_of_eq_three

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace StalkB4

section Loc
variable {K : Type} [Field K] (B : Subring K) (P : Ideal ↥B)

def loc (hP : P.IsPrime) : Subring K where
  carrier := {f | ∃ g h : ↥B, h ∉ P ∧ f * (h : K) = (g : K)}
  mul_mem' := by
    rintro a b ⟨g₁, h₁, hh₁, e₁⟩ ⟨g₂, h₂, hh₂, e₂⟩
    refine ⟨g₁ * g₂, h₁ * h₂, fun hm => (hP.mem_or_mem hm).elim hh₁ hh₂, ?_⟩
    push_cast
    calc a * b * ((h₁ : K) * h₂) = (a * h₁) * (b * h₂) := by ring
      _ = g₁ * g₂ := by rw [e₁, e₂]
  one_mem' := ⟨1, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  add_mem' := by
    rintro a b ⟨g₁, h₁, hh₁, e₁⟩ ⟨g₂, h₂, hh₂, e₂⟩
    refine ⟨g₁ * h₂ + g₂ * h₁, h₁ * h₂, fun hm => (hP.mem_or_mem hm).elim hh₁ hh₂, ?_⟩
    push_cast
    calc (a + b) * ((h₁ : K) * h₂) = (a * h₁) * h₂ + (b * h₂) * h₁ := by ring
      _ = g₁ * h₂ + g₂ * h₁ := by rw [e₁, e₂]
  zero_mem' := ⟨0, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  neg_mem' := by
    rintro a ⟨g, h, hh, e⟩
    exact ⟨-g, h, hh, by push_cast; rw [neg_mul, e]⟩

variable {B P}

theorem mem_loc_iff (hP : P.IsPrime) (f : K) :
    f ∈ loc B P hP ↔ ∃ g h : ↥B, h ∉ P ∧ f * (h : K) = (g : K) := Iff.rfl

theorem one_not_mem (hP : P.IsPrime) : (1 : ↥B) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem le_loc (hP : P.IsPrime) : B ≤ loc B P hP := fun f hf =>
  ⟨⟨f, hf⟩, 1, one_not_mem hP, by simp⟩

theorem coe_ne_zero_of_not_mem (hP : P.IsPrime) {h : ↥B} (hh : h ∉ P) : (h : K) ≠ 0 := by
  intro h0
  apply hh
  have : h = 0 := by exact_mod_cast h0
  rw [this]; exact P.zero_mem

theorem inv_mem_loc (hP : P.IsPrime) {h : ↥B} (hh : h ∉ P) : (h : K)⁻¹ ∈ loc B P hP :=
  ⟨1, h, hh, by rw [inv_mul_cancel₀ (coe_ne_zero_of_not_mem hP hh)]; simp⟩

@[reducible] def locAlgebra (hP : P.IsPrime) : Algebra ↥B ↥(loc B P hP) := (Subring.inclusion (le_loc hP)).toAlgebra

theorem locAlgebra_coe (hP : P.IsPrime) (b : ↥B) :
    ((@algebraMap ↥B ↥(loc B P hP) _ _ (locAlgebra hP) b : ↥(loc B P hP)) : K) = (b : K) := rfl

theorem isLocalization_loc (hP : P.IsPrime) :
    @IsLocalization _ _ P.primeCompl ↥(loc B P hP) _ (locAlgebra hP) := by
  letI := locAlgebra (B := B) (P := P) hP
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨h, hh⟩
    have hh' : h ∉ P := hh
    refine isUnit_iff_exists_inv.mpr ⟨⟨(h : K)⁻¹, inv_mem_loc hP hh'⟩, ?_⟩
    apply Subtype.ext
    change (h : K) * (h : K)⁻¹ = 1
    exact mul_inv_cancel₀ (coe_ne_zero_of_not_mem hP hh')
  · rintro ⟨s, g, h, hh, e⟩
    exact ⟨(g, ⟨h, hh⟩), Subtype.ext e⟩
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : K) = (y : K) := congrArg (fun z : ↥(loc B P hP) => (z : K)) hxy
    obtain rfl : x = y := Subtype.ext this
    rfl

theorem isUnit_loc_of_not_mem (hP : P.IsPrime) {g h : ↥B} (hg : g ∉ P) (hh : h ∉ P)
    (s : ↥(loc B P hP)) (hs : (s : K) * (h : K) = (g : K)) : IsUnit s := by
  have hs' : (s : K) = (g : K) * (h : K)⁻¹ := by
    rw [← hs, mul_inv_cancel_right₀ (coe_ne_zero_of_not_mem hP hh)]
  refine isUnit_iff_exists_inv.mpr ⟨⟨(h : K) * (g : K)⁻¹, ?_⟩, ?_⟩
  · exact ⟨h, g, hg, by rw [inv_mul_cancel_right₀ (coe_ne_zero_of_not_mem hP hg)]⟩
  · apply Subtype.ext
    change (s : K) * ((h : K) * (g : K)⁻¹) = 1
    rw [hs']
    field_simp [coe_ne_zero_of_not_mem hP hh, coe_ne_zero_of_not_mem hP hg]

end Loc

theorem isMaximal_of_ne_span {Ab B : Type} [CommRing Ab] [CommRing B] [Algebra Ab B]
    (ϖ : Ab) (P : Ideal B) [hP : P.IsPrime] (hϖP : algebraMap Ab B ϖ ∈ P)
    (hne : P ≠ Ideal.span {algebraMap Ab B ϖ})
    (hdim : Ring.KrullDimLE 1 (B ⧸ Ideal.span {algebraMap Ab B ϖ})) (hprime : Prime (algebraMap Ab B ϖ)) :
    P.IsMaximal := by
  set I : Ideal B := Ideal.span {algebraMap Ab B ϖ} with hI
  haveI : I.IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hIP : I ≤ P := by
    rw [Ideal.span_le]; exact Set.singleton_subset_iff.mpr hϖP
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
  set P' : Ideal (B ⧸ I) := P.map (Ideal.Quotient.mk I) with hP'
  haveI hP'p : P'.IsPrime := Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hIP)
  have hP'ne : P' ≠ ⊥ := by
    intro h
    rw [Ideal.map_eq_bot_iff_le_ker, hker] at h
    exact hne (le_antisymm h hIP)
  haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot hP'p hP'ne
  have hcomap : P'.comap (Ideal.Quotient.mk I) = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, hker]
    exact sup_eq_left.mpr hIP
  rw [← hcomap]
  exact Ideal.comap_isMaximal_of_surjective _ hsurj

theorem mk_comp_algebraMap_surjective {Ab B κ : Type} [CommRing Ab] [IsLocalRing Ab] [CommRing B] [Algebra Ab B]
    [Algebra.FiniteType Ab B] [Field κ] [IsAlgClosed κ]
    (resκ : Ab →+* κ) (hsurj : Function.Surjective resκ) (hker : RingHom.ker resκ = maximalIdeal Ab)
    (P : Ideal B) [hPm : P.IsMaximal] (hle : maximalIdeal Ab ≤ P.comap (algebraMap Ab B)) :
    Function.Surjective ((Ideal.Quotient.mk P).comp (algebraMap Ab B)) := by
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  letI alg : Algebra (ResidueField Ab) (B ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower Ab (ResidueField Ab) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType (ResidueField Ab) (B ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := Ab) (S := ResidueField Ab) (A := B ⧸ P)
  haveI : Module.Finite (ResidueField Ab) (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing _ _

  haveI : IsLocalHom resκ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ RingHom.ker resκ := by rw [hker]; exact (mem_maximalIdeal a).mpr hna
    rw [RingHom.mem_ker] at this
    rw [this] at ha
    exact not_isUnit_zero ha
  have hls : Function.Surjective (ResidueField.lift resκ) := by
    intro y
    obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨residue Ab a, by simp⟩
  haveI : IsAlgClosed (ResidueField Ab) :=
    IsAlgClosed.of_ringEquiv κ _
      (RingEquiv.ofBijective (ResidueField.lift resκ) ⟨(ResidueField.lift resκ).injective, hls⟩).symm
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField Ab) (K := B ⧸ P)
  intro y
  obtain ⟨x, hx⟩ := hbij.2 y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨a, by rw [← hx]; rfl⟩

section OrdCount
variable {κ F : Type} [Field κ] [Field F] [Algebra κ F] (Q : Place κ F)

theorem zpow_mem_iff {π : ↥Q.toValuationSubring} (hπ : Irreducible π) (n : ℤ) :
    (π : F) ^ n ∈ Q.toValuationSubring ↔ 0 ≤ n := by
  have hπ0 : (π : F) ≠ 0 := by
    intro h0; exact hπ.ne_zero (by exact_mod_cast h0)
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have h2 : (π : F) ^ (-n - 1) ∈ Q.toValuationSubring := by
      have : (-n - 1) = ((-n - 1).toNat : ℤ) := by omega
      rw [this, zpow_natCast]
      exact pow_mem π.2 _
    have h1 : (π : F)⁻¹ = (π : F) ^ n * (π : F) ^ (-n - 1) := by
      rw [← zpow_add₀ hπ0, ← zpow_neg_one]; congr 1; ring
    have h3 : (π : F)⁻¹ ∈ Q.toValuationSubring := by rw [h1]; exact mul_mem h h2
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨(π : F)⁻¹, h3⟩, ?_⟩
    apply Subtype.ext
    change (π : F) * (π : F)⁻¹ = 1
    exact mul_inv_cancel₀ hπ0
  · intro hn
    have : n = (n.toNat : ℤ) := by omega
    rw [this, zpow_natCast]
    exact pow_mem π.2 _

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ Q.toValuationSubring) (hf0 : f ≠ 0) : 0 ≤ Q.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥Q.toValuationSubring
  obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hf0 hπ
  have key : (π : F) ^ Q.ord f = (((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring) : F) * f := by
    have h1 : (((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring) : F) *
        (((u : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring) : F) = 1 := by
      rw [← Subring.coe_mul, Units.inv_mul]; rfl
    conv_rhs => rw [hu, ← mul_assoc, h1, one_mul]
  rw [← zpow_mem_iff Q hπ, key]
  exact mul_mem ((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring).2 hf

theorem ord_eq_zero_of_isUnit {f : F} (hf : f ∈ Q.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : ↥Q.toValuationSubring)) : Q.ord f = 0 := by
  obtain ⟨u, hu⟩ := hu
  have : f = ((u : ↥Q.toValuationSubring) : F) := by rw [hu]
  rw [this]; exact Q.ord_coe_unit u

theorem one_le_ord_of_not_isUnit {f : F} (hf : f ∈ Q.toValuationSubring) (hf0 : f ≠ 0)
    (hu : ¬ IsUnit (⟨f, hf⟩ : ↥Q.toValuationSubring)) : 1 ≤ Q.ord f := by
  have h0 := ord_nonneg_of_mem Q hf hf0
  by_contra hlt
  have hz : Q.ord f = 0 := by omega
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥Q.toValuationSubring
  obtain ⟨u, hu'⟩ := Q.exists_unit_mul_zpow hf0 hπ
  rw [hz, zpow_zero, mul_one] at hu'
  apply hu
  have : (⟨f, hf⟩ : ↥Q.toValuationSubring) = (u : ↥Q.toValuationSubring) := Subtype.ext hu'
  rw [this]; exact Units.isUnit u

theorem ord_eq_one_of_count (t : F) (ht : t ∈ Q.toValuationSubring) (ht0 : t ≠ 0)
    (htu : ¬ IsUnit (⟨t, ht⟩ : ↥Q.toValuationSubring))
    (M : Set F) (hM : ∀ m ∈ M, m ∈ Q.toValuationSubring)
    (hstep : ∀ m (hm : m ∈ M), m ≠ 0 → IsUnit (⟨m, hM m hm⟩ : ↥Q.toValuationSubring) ∨ ∃ m' ∈ M, m = t * m')
    (hfrac : ∀ x : F, ∃ g ∈ M, ∃ h ∈ M, h ≠ 0 ∧ x * h = g) : Q.ord t = 1 := by
  set c : ℤ := Q.ord t with hc
  have hc1 : 1 ≤ c := one_le_ord_of_not_isUnit Q ht ht0 htu

  have claim : ∀ n : ℕ, ∀ m (hm : m ∈ M), m ≠ 0 → (Q.ord m).toNat = n → c ∣ Q.ord m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hm hm0 hn
      rcases hstep m hm hm0 with hunit | ⟨m', hm', rfl⟩
      · rw [ord_eq_zero_of_isUnit Q (hM m hm) hunit]; exact dvd_zero c
      · have hm'0 : m' ≠ 0 := by rintro rfl; exact hm0 (mul_zero t)
        have h0' := ord_nonneg_of_mem Q (hM m' hm') hm'0
        have hmul : Q.ord (t * m') = c + Q.ord m' := by rw [Q.ord_mul ht0 hm'0]
        have hlt : (Q.ord m').toNat < n := by
          rw [← hn, hmul]; omega
        have := ih _ hlt m' hm' hm'0 rfl
        rw [hmul]; exact dvd_add (dvd_refl c) this
  have hdvd : ∀ x : F, x ≠ 0 → c ∣ Q.ord x := by
    intro x hx
    obtain ⟨g, hg, h, hh, hh0, e⟩ := hfrac x
    have hg0 : g ≠ 0 := by rw [← e]; exact mul_ne_zero hx hh0
    have h1 := claim _ g hg hg0 rfl
    have h2 := claim _ h hh hh0 rfl
    have : Q.ord x = Q.ord g - Q.ord h := by rw [← e, Q.ord_mul hx hh0]; ring
    rw [this]; exact dvd_sub h1 h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥Q.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    intro h0; exact hπ.ne_zero (by exact_mod_cast h0)
  have h1 := hdvd (π : F) hπ0
  rw [Q.ord_coe_irreducible hπ] at h1
  have : c ≤ 1 := Int.le_of_dvd one_pos h1
  omega

end OrdCount

theorem exists_ringHom_lift {S κ E : Type} [CommRing S] [Field κ] [Field E] [Algebra κ E]
    (ψ : S →+* E) (h : ∀ s, ∃ c : κ, algebraMap κ E c = ψ s) :
    ∃ χ : S →+* κ, ∀ s, algebraMap κ E (χ s) = ψ s := by
  classical
  have hinj := (algebraMap κ E).injective
  have h1 : (h 1).choose = 1 := by
    apply hinj; rw [(h 1).choose_spec, map_one, map_one]
  have hm : ∀ x y, (h (x * y)).choose = (h x).choose * (h y).choose := by
    intro x y; apply hinj; rw [(h _).choose_spec, map_mul, map_mul, (h x).choose_spec, (h y).choose_spec]
  have h0 : (h 0).choose = 0 := by
    apply hinj; rw [(h 0).choose_spec, map_zero, map_zero]
  have ha : ∀ x y, (h (x + y)).choose = (h x).choose + (h y).choose := by
    intro x y; apply hinj; rw [(h _).choose_spec, map_add, map_add, (h x).choose_spec, (h y).choose_spec]
  let χ : S →+* κ :=
    { toFun := fun s => (h s).choose
      map_one' := h1
      map_mul' := hm
      map_zero' := h0
      map_add' := ha }
  exact ⟨χ, fun s => (h s).choose_spec⟩

end StalkB4

open StalkB4 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (halgc : IsAlgClosed (ResidueField ↥A))

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (hdvrb : IsDiscreteValuationRing ↥Ab) (hhensb : HenselianLocalRing ↥Ab)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),
        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) → (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg → @Algebra.FinitePresentation ↥Ab ↥B _ _ alg →
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) →
        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) → Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) →
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        ∀ (hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers)

          (hfracB : ∀ x : FSS, ∃ g h : ↥B, R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ≠ 0 ∧ x * R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ = R.residue ⟨((g : ↥B) : ↥(fieldBar q M')), hBR _ (g).2⟩)
          (Q : Place (ResidueField ↥A) FSS) (hQ : ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring),
        ∃ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥Ab →+* ↥S) (χ : ↥S →+* ResidueField ↥A),

        (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ S) ∧
        (∀ a : ↥Ab, ((φ (Polynomial.C a) : ↥S) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
        (∀ a : ↥Ab, χ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
        χ (φ Polynomial.X) = 0 ∧

        (∃ _ : IsLocalRing ↥S, RingHom.ker χ = maximalIdeal ↥S) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ S → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥S, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧ (φ).EssFiniteType ∧

        (∃ hSR : ∀ f : ↥S, (f : ↥(fieldBar q M')) ∈ R.integers,
          ∀ f : ↥S, (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φ (Polynomial.C ϖb) ∣ f) ∧

        (∀ f : ↥S, ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
          IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
            algebraMap (ResidueField ↥A) Q.ResidueField (χ f)) ∧
        (∃ hR : ((φ Polynomial.X : ↥S) : ↥(fieldBar q M')) ∈ R.integers,
          Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : ↥(fieldBar q M')), hR⟩) = 1) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ S) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ S ↔ ∃ g h : ↥B, (∃ hm : R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩, hm⟩ ≠ 0) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) := by
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ W₀ htop hlin B alg hAB hBF₁ hfracF₁ hsm hfp hdim hBW₀ hprime hW₀ FSS instF instAF R hRW₀ hBR hfracB Q hQ
  classical
  letI : Algebra ↥Ab ↥B := alg
  haveI : Algebra.FormallySmooth ↥Ab ↥B := hsm
  haveI : Algebra.FinitePresentation ↥Ab ↥B := hfp
  haveI : IsDiscreteValuationRing ↥Ab := hdvrb
  haveI : IsAlgClosed (ResidueField ↥A) := halgc

  set ϖB : ↥B := algebraMap ↥Ab ↥B ϖb with hϖB
  have hϖbmax : ϖb ∈ maximalIdeal ↥Ab := by rw [hϖb]; exact Ideal.mem_span_singleton_self ϖb
  let inclA : ↥Ab →+* ↥A :=
    { toFun := fun a => ⟨((a : ↥Kb) : AlgebraicClosure ℚ), (hAb a).mp a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have inclA_coe : ∀ a : ↥Ab, (inclA a : AlgebraicClosure ℚ) = ((a : ↥Kb) : AlgebraicClosure ℚ) := fun _ => rfl
  have hunitA : ∀ a : ↥Ab, IsUnit (inclA a) → IsUnit a := by
    intro a ha
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
    have hb' : ((a : ↥Kb) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hb
      have h__ := this
      try simp at h__
      try simp
      exact h__
    have ha0 : ((a : ↥Kb) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; rw [h, zero_mul] at hb'; exact zero_ne_one hb'
    have hbeq : (b : AlgebraicClosure ℚ) = ((a : ↥Kb) : AlgebraicClosure ℚ)⁻¹ :=
      eq_inv_of_mul_eq_one_right hb'
    have hbK : (b : AlgebraicClosure ℚ) ∈ Kb := by rw [hbeq]; exact inv_mem (a : ↥Kb).2
    have hbA : (⟨(b : AlgebraicClosure ℚ), hbK⟩ : ↥Kb) ∈ Ab := (hAb _).mpr b.2
    refine isUnit_iff_exists_inv.mpr ⟨⟨⟨(b : AlgebraicClosure ℚ), hbK⟩, hbA⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    exact hb'
  let resκ : ↥Ab →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp inclA
  have resκ_apply : ∀ a, resκ a = IsLocalRing.residue ↥A (inclA a) := fun _ => rfl
  have hresκ : Function.Surjective resκ := by
    intro y
    obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, hcA, hsub, hm⟩ := hκ (a' : AlgebraicClosure ℚ) a'.2
    have hcK : (c : AlgebraicClosure ℚ) ∈ Kb := Kb.algebraMap_mem c
    refine ⟨⟨⟨(c : AlgebraicClosure ℚ), hcK⟩, (hAb _).mpr hcA⟩, ?_⟩
    rw [resκ_apply, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have : a' - inclA ⟨⟨(c : AlgebraicClosure ℚ), hcK⟩, (hAb _).mpr hcA⟩ = ⟨(a' : AlgebraicClosure ℚ) - c, hsub⟩ :=
      Subtype.ext rfl
    rw [this]; exact hm
  have hkerκ : RingHom.ker resκ = maximalIdeal ↥Ab := by
    ext a
    rw [RingHom.mem_ker, resκ_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_congr ⟨hunitA a, fun h => h.map inclA⟩
  have hκϖ : resκ ϖb = 0 := by
    have : ϖb ∈ RingHom.ker resκ := by rw [hkerκ]; exact hϖbmax
    exact this

  let toO : ↥B →+* ↥R.integers := (B.subtype).codRestrict R.integers (fun b => hBR _ b.2)
  have toO_apply : ∀ b : ↥B, toO b = ⟨(b : ↥(fieldBar q M')), hBR _ b.2⟩ := fun _ => rfl
  let resB : ↥B →+* FSS := R.residue.comp toO
  have resB_apply : ∀ b : ↥B, resB b = R.residue ⟨(b : ↥(fieldBar q M')), hBR _ b.2⟩ := fun _ => rfl
  have hQ' : ∀ b : ↥B, resB b ∈ Q.toValuationSubring := hQ
  have hfracB' : ∀ x : FSS, ∃ g h : ↥B, resB h ≠ 0 ∧ x * resB h = resB g := hfracB
  let toOQ : ↥B →+* ↥Q.toValuationSubring := resB.codRestrict Q.toValuationSubring hQ'
  have toOQ_coe : ∀ b : ↥B, (toOQ b : FSS) = resB b := fun _ => rfl
  let χB : ↥B →+* Q.ResidueField := (IsLocalRing.residue ↥Q.toValuationSubring).comp toOQ
  have χB_apply : ∀ b : ↥B, χB b = IsLocalRing.residue _ (toOQ b) := fun _ => rfl
  set 𝔫 : Ideal ↥B := RingHom.ker χB with h𝔫
  have h𝔫p : 𝔫.IsPrime := by rw [h𝔫]; exact RingHom.ker_isPrime χB
  have mem𝔫 : ∀ b : ↥B, b ∈ 𝔫 ↔ toOQ b ∈ maximalIdeal ↥Q.toValuationSubring := fun b => by
    rw [h𝔫, RingHom.mem_ker, χB_apply]; exact IsLocalRing.residue_eq_zero_iff _
  have unit_of_not_mem𝔫 : ∀ b : ↥B, b ∉ 𝔫 → IsUnit (toOQ b) := fun b hb => by
    rw [mem𝔫, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hb; exact hb

  have hcompat : ∀ a : ↥Ab, resB (algebraMap ↥Ab ↥B a) = algebraMap (ResidueField ↥A) FSS (resκ a) := by
    intro a
    rw [resB_apply, resκ_apply]
    have h1 : (⟨((algebraMap ↥Ab ↥B a : ↥B) : ↥(fieldBar q M')), hBR _ (algebraMap ↥Ab ↥B a).2⟩ : ↥R.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (inclA a : AlgebraicClosure ℚ),
            (R.algebraMap_mem_iff _).mpr (inclA a).2⟩ :=
      Subtype.ext (hAB a)
    rw [h1]
    exact R.residue_algebraMap (inclA a)
  have hresϖ : resB ϖB = 0 := by
    rw [hϖB, hcompat, hκϖ, map_zero]
  have hϖO : toO ϖB ∈ maximalIdeal ↥R.integers := by
    rw [← R.ker_residue, RingHom.mem_ker]; exact hresϖ

  have hBm : ∀ b : ↥B, toO b ∈ maximalIdeal ↥R.integers ↔ ϖB ∣ b := by
    intro b
    constructor
    · intro hb
      by_contra hndvd
      have hb0 : (b : ↥(fieldBar q M')) ≠ 0 := by
        intro h0; apply hndvd
        have : b = 0 := by exact_mod_cast h0
        rw [this]; exact dvd_zero _
      obtain ⟨hbF₀, hbW₀⟩ := hBW₀ (b : ↥(fieldBar q M')) b.2
      have hinvW : (⟨(b : ↥(fieldBar q M')), hbF₀⟩⁻¹ : ↥F₀) ∈ W₀ := by
        refine (hW₀ _).mpr ⟨1, b, hndvd, ?_⟩
        rw [IntermediateField.coe_inv]
        push_cast
        exact inv_mul_cancel₀ hb0
      have hinvO : (b : ↥(fieldBar q M'))⁻¹ ∈ R.integers := by
        have := (hRW₀ _).mpr hinvW
        rwa [IntermediateField.coe_inv] at this
      apply (IsLocalRing.mem_maximalIdeal _).mp hb
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinvO⟩, ?_⟩
      apply Subtype.ext
      change (b : ↥(fieldBar q M')) * (b : ↥(fieldBar q M'))⁻¹ = 1
      exact mul_inv_cancel₀ hb0
    · rintro ⟨c, rfl⟩
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ hϖO

  have hϖ𝔫 : ϖB ∈ 𝔫 := by
    have : toOQ ϖB = 0 := Subtype.ext hresϖ
    rw [h𝔫, RingHom.mem_ker, χB_apply, this, map_zero]

  have hne : 𝔫 ≠ Ideal.span {ϖB} := by
    intro heq
    apply Q.ne_top'
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, h, hh0, e⟩ := hfracB' x
    have hhn : h ∉ 𝔫 := by
      rw [heq, Ideal.mem_span_singleton]
      intro hdvd
      apply hh0
      have : toO h ∈ maximalIdeal _ := (hBm h).mpr hdvd
      rw [← R.ker_residue, RingHom.mem_ker] at this
      exact this
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp (unit_of_not_mem𝔫 h hhn)
    have hw' : resB h * (w : FSS) = 1 := by
      have := congrArg (fun z : ↥Q.toValuationSubring => (z : FSS)) hw
      have h__ := this
      try simp at h__
      try simp
      exact h__
    have : x = resB g * (w : FSS) := by
      calc x = x * (resB h * w) := by rw [hw', mul_one]
        _ = (x * resB h) * w := by ring
        _ = resB g * w := by rw [e]
    rw [this]
    exact mul_mem (hQ' g) w.2

  haveI h𝔫m : 𝔫.IsMaximal := @isMaximal_of_ne_span _ _ _ _ _ ϖb 𝔫 h𝔫p hϖ𝔫 hne hdim hprime
  have hle𝔪 : maximalIdeal ↥Ab ≤ 𝔫.comap (algebraMap ↥Ab ↥B) := by
    intro a ha
    rw [hϖb, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [Ideal.mem_comap, map_mul]
    exact Ideal.mul_mem_right _ _ hϖ𝔫
  have hrat : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap ↥Ab ↥B)) :=
    mk_comp_algebraMap_surjective resκ hresκ hkerκ 𝔫 hle𝔪

  let S : Subring ↥(fieldBar q M') := loc B 𝔫 h𝔫p
  letI algBS : Algebra ↥B ↥S := locAlgebra h𝔫p
  haveI : IsLocalization.AtPrime ↥S 𝔫 := isLocalization_loc h𝔫p
  haveI : IsLocalRing ↥S := IsLocalization.AtPrime.isLocalRing ↥S 𝔫
  have algBS_coe : ∀ b : ↥B, ((algebraMap ↥B ↥S b : ↥S) : ↥(fieldBar q M')) = b := fun _ => rfl
  have hBS : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ S := fun f hf => le_loc h𝔫p hf
  obtain ⟨t, ht𝔫, hmS, hφs, hφu, hφe⟩ :=
    Algebra.FormallySmooth.exists_etaleCoordinate_of_krullDimLE_one (S := ↥S) ϖb hϖb hprime hdim 𝔫 hϖ𝔫 hne hrat
  let φ : Polynomial ↥Ab →+* ↥S :=
    Polynomial.eval₂RingHom ((algebraMap ↥B ↥S).comp (algebraMap ↥Ab ↥B)) (algebraMap ↥B ↥S t)
  have hφC : ∀ a, φ (Polynomial.C a) = algebraMap ↥B ↥S (algebraMap ↥Ab ↥B a) := fun a => by
    simp [φ, Polynomial.coe_eval₂RingHom]
  have hφX : φ Polynomial.X = algebraMap ↥B ↥S t := by simp [φ, Polynomial.coe_eval₂RingHom]

  have hSO : ∀ f : ↥S, (f : ↥(fieldBar q M')) ∈ R.integers := by
    rintro ⟨f, g, h, hh, e⟩
    have hu : IsUnit (toO h) := by
      apply R.isUnit_of_residue_ne_zero
      intro h0
      exact (unit_of_not_mem𝔫 h hh).ne_zero (Subtype.ext h0)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hw' : (h : ↥(fieldBar q M')) * (w : ↥(fieldBar q M')) = 1 := by
      have := congrArg (fun z : ↥R.integers => (z : ↥(fieldBar q M'))) hw
      have h__ := this
      try simp at h__
      try simp
      exact h__
    have : f = (g : ↥(fieldBar q M')) * (w : ↥(fieldBar q M')) := by
      calc f = f * ((h : ↥(fieldBar q M')) * w) := by rw [hw', mul_one]
        _ = (f * h) * w := by ring
        _ = g * w := by rw [e]
    show f ∈ R.integers
    rw [this]; exact mul_mem (hBR _ g.2) w.2
  let toOS : ↥S →+* ↥R.integers := (S.subtype).codRestrict R.integers hSO
  have toOS_B : ∀ b : ↥B, toOS (algebraMap ↥B ↥S b) = toO b := fun _ => rfl
  let resS : ↥S →+* FSS := R.residue.comp toOS
  have resS_apply : ∀ f : ↥S, resS f = R.residue ⟨(f : ↥(fieldBar q M')), hSO f⟩ := fun _ => rfl
  have resS_B : ∀ b : ↥B, resS (algebraMap ↥B ↥S b) = resB b := fun _ => rfl
  have resS_frac : ∀ (f : ↥S) (g h : ↥B), (f : ↥(fieldBar q M')) * h = g → resS f * resB h = resB g := by
    intro f g h e
    have e' : toOS f * toO h = toO g := Subtype.ext e
    have := congrArg R.residue e'
    rwa [map_mul] at this
  have hresSQ : ∀ f : ↥S, resS f ∈ Q.toValuationSubring := by
    intro f
    obtain ⟨g, h, hh, e⟩ := f.2
    have e'' := resS_frac f g h e
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp (unit_of_not_mem𝔫 h hh)
    have hw' : resB h * (w : FSS) = 1 := by
      have := congrArg (fun z : ↥Q.toValuationSubring => (z : FSS)) hw
      have h__ := this
      try simp at h__
      try simp
      exact h__
    have : resS f = resB g * (w : FSS) := by
      calc resS f = resS f * (resB h * w) := by rw [hw', mul_one]
        _ = (resS f * resB h) * w := by ring
        _ = resB g * w := by rw [e'']
    rw [this]; exact mul_mem (hQ' g) w.2
  let toOQS : ↥S →+* ↥Q.toValuationSubring := resS.codRestrict Q.toValuationSubring hresSQ
  let ψ : ↥S →+* Q.ResidueField := (IsLocalRing.residue _).comp toOQS
  have ψ_apply : ∀ f : ↥S, ψ f = IsLocalRing.residue _ (toOQS f) := fun _ => rfl
  have ψ_B : ∀ b : ↥B, ψ (algebraMap ↥B ↥S b) = χB b := fun _ => rfl
  have ψ_frac : ∀ (f : ↥S) (g h : ↥B), (f : ↥(fieldBar q M')) * h = g → ψ f * χB h = χB g := by
    intro f g h e
    have e' : f * algebraMap ↥B ↥S h = algebraMap ↥B ↥S g := Subtype.ext e
    have := congrArg ψ e'
    rwa [map_mul, ψ_B, ψ_B] at this
  have χB_alg : ∀ a : ↥Ab, χB (algebraMap ↥Ab ↥B a) = algebraMap (ResidueField ↥A) Q.ResidueField (resκ a) := by
    intro a
    have h1 : toOQ (algebraMap ↥Ab ↥B a) = algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (resκ a) :=
      Subtype.ext (by rw [Place.coe_algebraMap]; exact hcompat a)
    rw [χB_apply, h1, IsScalarTower.algebraMap_apply (ResidueField ↥A) ↥Q.toValuationSubring Q.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]

  have hkerψ : ∀ f : ↥S, ψ f = 0 ↔ f ∈ maximalIdeal ↥S := by
    intro f
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hf hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      have : ψ f * ψ w = 1 := by rw [← map_mul, hw, map_one]
      rw [hf, zero_mul] at this
      exact zero_ne_one this
    · intro hns
      obtain ⟨g, h, hh, e⟩ := f.2
      by_contra hψ
      apply hns
      have hg : g ∉ 𝔫 := by
        intro hg
        apply hψ
        have e' := ψ_frac f g h e
        have hg0 : χB g = 0 := by rw [h𝔫] at hg; exact hg
        have hh0 : χB h ≠ 0 := fun h0 => hh (by rw [h𝔫]; exact h0)
        rw [hg0] at e'
        exact (mul_eq_zero.mp e').resolve_right hh0
      exact isUnit_loc_of_not_mem h𝔫p hg hh f e

  have hχex : ∀ f : ↥S, ∃ c : ResidueField ↥A, algebraMap (ResidueField ↥A) Q.ResidueField c = ψ f := by
    intro f
    obtain ⟨g, h, hh, e⟩ := f.2
    have hrepr : ∀ b : ↥B, ∃ a : ↥Ab, χB b = algebraMap (ResidueField ↥A) Q.ResidueField (resκ a) := by
      intro b
      obtain ⟨a, ha⟩ := hrat (Ideal.Quotient.mk 𝔫 b)
      refine ⟨a, ?_⟩
      rw [← χB_alg]
      have hmem : algebraMap ↥Ab ↥B a - b ∈ 𝔫 := by
        rw [← Ideal.Quotient.eq]; exact ha
      rw [h𝔫, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
      exact hmem.symm
    obtain ⟨ag, hag⟩ := hrepr g
    obtain ⟨ah, hah⟩ := hrepr h
    have hh0 : χB h ≠ 0 := fun h0 => hh (by rw [h𝔫]; exact h0)
    have e' := ψ_frac f g h e
    refine ⟨resκ ag / resκ ah, ?_⟩
    rw [map_div₀, ← hag, ← hah, ← e', mul_div_cancel_right₀ _ hh0]
  obtain ⟨χ, hχ⟩ := exists_ringHom_lift ψ hχex
  have hχ_inj := (algebraMap (ResidueField ↥A) Q.ResidueField).injective

  have ht0 : resB t ≠ 0 := by
    intro h0
    have htm : toO t ∈ maximalIdeal _ := by rw [← R.ker_residue, RingHom.mem_ker]; exact h0
    obtain ⟨t', ht'⟩ := (hBm t).mp htm
    apply hne
    refine le_antisymm ?_ ?_
    · intro b hb
      rw [Ideal.mem_span_singleton]
      have hb' : χB b = 0 := by rw [h𝔫] at hb; exact hb
      have hbS : algebraMap ↥B ↥S b ∈ maximalIdeal ↥S := (hkerψ _).mp (by rw [ψ_B]; exact hb')
      rw [hmS, ht', map_mul, Ideal.mem_span_pair] at hbS
      obtain ⟨a, c, hac⟩ := hbS
      set y : ↥S := a + c * algebraMap ↥B ↥S t' with hy
      have hby : algebraMap ↥B ↥S b = algebraMap ↥B ↥S ϖB * y := by rw [← hac, hy]; ring
      obtain ⟨g, h, hh, e⟩ := y.2
      have key : b * h = ϖB * g := by
        apply Subtype.ext
        have h2 := congrArg (fun z : ↥S => (z : ↥(fieldBar q M'))) hby
        simp only [algBS_coe, Subring.coe_mul] at h2
        push_cast
        rw [h2, mul_assoc, e]
      have hdvd : ϖB ∣ b * h := ⟨g, key⟩
      rcases hprime.dvd_or_dvd hdvd with hb1 | hh1
      · exact hb1
      · exfalso; apply hh
        obtain ⟨d, rfl⟩ := hh1
        exact Ideal.mul_mem_right _ _ hϖ𝔫
    · rw [Ideal.span_le]; exact Set.singleton_subset_iff.mpr hϖ𝔫
  have htu : ¬ IsUnit (⟨resB t, hQ' t⟩ : ↥Q.toValuationSubring) := by
    have := (mem𝔫 t).mp ht𝔫
    exact (IsLocalRing.mem_maximalIdeal _).mp this
  have hordt : Q.ord (resB t) = 1 := by
    refine ord_eq_one_of_count Q (resB t) (hQ' t) ht0 htu (Set.range fun f : ↥S => resS f) ?_ ?_ ?_
    · rintro _ ⟨f, rfl⟩; exact hresSQ f
    · rintro _ ⟨f, rfl⟩ hf0
      by_cases hfu : IsUnit f
      · left; exact hfu.map toOQS
      · right
        have hfm : f ∈ maximalIdeal ↥S := (IsLocalRing.mem_maximalIdeal _).mpr hfu
        rw [hmS, Ideal.mem_span_pair] at hfm
        obtain ⟨a, b, hab⟩ := hfm
        refine ⟨resS b, ⟨b, rfl⟩, ?_⟩
        beta_reduce
        rw [← hab, map_add, map_mul, map_mul, resS_B, resS_B, ← hϖB, hresϖ]; ring
    · intro x
      obtain ⟨g, h, hh0, e⟩ := hfracB' x
      exact ⟨resB g, ⟨algebraMap ↥B ↥S g, resS_B g⟩, resB h, ⟨algebraMap ↥B ↥S h, resS_B h⟩, hh0, e⟩

  refine ⟨S, φ, χ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hφs, hφu, hφe, ⟨hSO, ?_⟩, ?_, ?_, hBS, ?_⟩

  · intro a
    rw [← hAB a]; exact hBS _ (algebraMap ↥Ab ↥B a).2

  · intro a
    rw [hφC, algBS_coe, hAB]

  · intro a
    apply hχ_inj
    rw [hχ, hφC, ψ_B, χB_alg]
    rfl

  · apply hχ_inj
    rw [hχ, hφX, ψ_B, map_zero]
    rw [h𝔫] at ht𝔫; exact ht𝔫

  · refine ⟨inferInstance, ?_⟩
    ext f
    rw [RingHom.mem_ker, ← hkerψ, ← hχ f, map_eq_zero_iff _ hχ_inj]

  · rintro f ⟨g, h, hh, e⟩
    have hh0 := coe_ne_zero_of_not_mem h𝔫p hh
    have : f = (g : ↥(fieldBar q M')) * (h : ↥(fieldBar q M'))⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hh0]
    rw [this]
    exact mul_mem (hBF₁ _ g.2) (inv_mem (hBF₁ _ h.2))

  · intro f hf
    obtain ⟨g, h, hh0, e⟩ := hfracF₁ f hf
    exact ⟨⟨g, hBS _ g.2⟩, ⟨h, hBS _ h.2⟩, hh0, e⟩

  · intro f
    rw [hφC, ← hϖB]
    constructor
    · intro hf
      obtain ⟨g, h, hh, e⟩ := f.2
      have e' : toOS f * toO h = toO g := Subtype.ext e
      have hgm : toO g ∈ maximalIdeal ↥R.integers := by
        rw [← e']; exact Ideal.mul_mem_right _ _ hf
      obtain ⟨g', hg'⟩ := (hBm g).mp hgm
      have hh0 := coe_ne_zero_of_not_mem h𝔫p hh
      refine ⟨⟨(g' : ↥(fieldBar q M')) * (h : ↥(fieldBar q M'))⁻¹, g', h, hh,
        by rw [inv_mul_cancel_right₀ hh0]⟩, ?_⟩
      apply Subtype.ext
      show (f : ↥(fieldBar q M')) = (ϖB : ↥(fieldBar q M')) * ((g' : ↥(fieldBar q M')) * (h : ↥(fieldBar q M'))⁻¹)
      have : (f : ↥(fieldBar q M')) = (g : ↥(fieldBar q M')) * (h : ↥(fieldBar q M'))⁻¹ := by
        rw [← e, mul_inv_cancel_right₀ hh0]
      rw [this, hg']; push_cast; ring
    · rintro ⟨c, hc⟩
      have : toOS f = toO ϖB * toOS c :=
        Subtype.ext (by
          have h := congrArg (fun z : ↥S => (z : ↥(fieldBar q M'))) hc
          simp only [toOS, toO] at h ⊢
          exact h)
      show toOS f ∈ maximalIdeal _
      rw [this]; exact Ideal.mul_mem_right _ _ hϖO

  · intro f
    exact ⟨hSO f, hresSQ f, (hχ f).symm⟩

  · refine ⟨hSO _, ?_⟩
    have : (⟨((φ Polynomial.X : ↥S) : ↥(fieldBar q M')), hSO _⟩ : ↥R.integers) = toO t :=
      Subtype.ext (by rw [hφX]; rfl)
    rw [this]; exact hordt

  · intro f
    constructor
    · rintro ⟨g, h, hh, e⟩
      exact ⟨g, h, ⟨hQ' h, (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (unit_of_not_mem𝔫 h hh)⟩, e⟩
    · rintro ⟨g, h, ⟨hm, hne0⟩, e⟩
      refine ⟨g, h, fun hh => hne0 ?_, e⟩
      exact (IsLocalRing.residue_eq_zero_iff _).mpr ((mem𝔫 h).mp hh)

end S_ModularCurve_FullLevel_supersingularProlongation_smoothPointStalk_of_affineChart_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointStalk_of_affineChart_of_eq_three (solution)
