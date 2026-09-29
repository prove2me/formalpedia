-- Prove2me | solution 1 for NumberField.finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2c7e4b1e-6aa7-569a-93cd-2166e570bbca

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

namespace SignFixedFieldFrobenius

attribute [local instance] Ideal.Quotient.field

open Polynomial in

theorem card_le_of_forall_pow_eq {K : Type*} [CommRing K] [IsDomain K] [Finite K]
    {n : ℕ} (hn : 1 < n) (h : ∀ x : K, x ^ n = x) : Nat.card K ≤ n := by
  cases nonempty_fintype K
  have hdeg : (X ^ n - X : K[X]).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; exact hn),
      natDegree_X_pow]
  have hne : (X ^ n - X : K[X]) ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hdeg]
  refine card_le_degree_of_subset_roots fun x _ ↦ ?_
  rw [mem_roots hne]
  simp [Polynomial.IsRoot, h x]

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]
variable (F : IntermediateField E L)

omit [NumberField E] [NumberField L] in

theorem algebraMap_restrictNormal_smul [Normal E F] (σ : L ≃ₐ[E] L) (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 L) (σ.restrictNormal F • x) = σ • algebraMap (𝓞 F) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  show algebraMap F L ((σ.restrictNormal F) (x : F)) = σ (algebraMap F L (x : F))
  exact AlgEquiv.restrictNormal_commutes σ F (x : F)

theorem isArithFrobAt_restrictNormal [IsGalois E L] [IsGalois E F] (Q : Ideal (𝓞 L))
    (σ : L ≃ₐ[E] L)
    (hσ : IsArithFrobAt (𝓞 E) σ Q) :
    IsArithFrobAt (𝓞 E) (σ.restrictNormal F) (Q.under (𝓞 F)) := by
  intro x
  rw [Ideal.under_under, Ideal.mem_comap, map_sub, map_pow]
  have := hσ (algebraMap (𝓞 F) (𝓞 L) x)
  simpa [algebraMap_restrictNormal_smul] using this

theorem isSeparable_quotient (P : Ideal (𝓞 E)) (W : Ideal (𝓞 F)) [P.IsMaximal] [W.IsMaximal]
    [W.LiesOver P] : Algebra.IsSeparable (𝓞 E ⧸ P) (𝓞 F ⧸ W) := by
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField E)
  have hW : W ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField F)
  haveI : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  haveI : Finite (𝓞 F ⧸ W) := Ring.HasFiniteQuotients.finiteQuotient hW
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem ramificationIdxIn_eq_one [IsGalois E L] [IsGalois E F] (v : HeightOneSpectrum (𝓞 E))
    (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1) (w : HeightOneSpectrum (𝓞 F))
    (hw : w.under (𝓞 E) = v) : Ideal.ramificationIdxIn v.asIdeal (𝓞 F) = 1 := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  have := Ideal.ramificationIdxIn_mul_ramificationIdxIn' (p := v.asIdeal) w.asIdeal (F ≃ₐ[E] F)
    (𝓞 L) (L ≃ₐ[E] L) (L ≃ₐ[F] L)
  rw [hv] at this
  exact Nat.eq_one_of_mul_eq_one_right this

theorem inertia_eq_bot [IsGalois E L] [IsGalois E F] (v : HeightOneSpectrum (𝓞 E))
    (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1) (w : HeightOneSpectrum (𝓞 F))
    (hw : w.under (𝓞 E) = v) : Ideal.inertia (F ≃ₐ[E] F) w.asIdeal = ⊥ := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI := isSeparable_quotient F v.asIdeal w.asIdeal
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[E] F) v.asIdeal
    w.asIdeal
  rw [ramificationIdxIn_eq_one F v hv w hw] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

theorem isArithFrobAt_one_iff [IsGalois E F] (P : Ideal (𝓞 E)) (W : Ideal (𝓞 F)) [P.IsMaximal]
    [W.IsMaximal] [W.LiesOver P] :
    IsArithFrobAt (𝓞 E) (1 : F ≃ₐ[E] F) W ↔ P.inertiaDeg' W = 1 := by
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField E)
  have hW : W ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField F)
  haveI : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  haveI : Finite (𝓞 F ⧸ W) := Ring.HasFiniteQuotients.finiteQuotient hW
  have hunder : W.under (𝓞 E) = P := (Ideal.LiesOver.over (P := W) (p := P)).symm
  have hq : 1 < Nat.card (𝓞 E ⧸ P) := Finite.one_lt_card
  have hcardW : Nat.card (𝓞 F ⧸ W) = Nat.card (𝓞 E ⧸ P) ^ P.inertiaDeg' W := by
    rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ P)]
  constructor
  · intro h
    have hle : Nat.card (𝓞 F ⧸ W) ≤ Nat.card (𝓞 E ⧸ P) := by
      refine card_le_of_forall_pow_eq hq fun y ↦ ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have := h.mk_apply x
      rw [hunder] at this
      simpa using this.symm
    rw [hcardW] at hle
    have hf : P.inertiaDeg' W ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have := Nat.pow_lt_pow_right hq hcon
      rw [pow_one] at this
      omega
    have hf0 : P.inertiaDeg' W ≠ 0 := Ideal.inertiaDeg_ne_zero P W
    omega
  · intro hf x
    rw [hunder, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
    have hcard : Nat.card (𝓞 F ⧸ W) = Nat.card (𝓞 E ⧸ P) := by rw [hcardW, hf, pow_one]
    cases nonempty_fintype (𝓞 F ⧸ W)
    rw [← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
    simp

theorem restrictNormal_eq_one_iff_inertiaDeg_under_eq_one [IsGalois E L] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1)
    (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 E) = v)
    (σ : L ≃ₐ[E] L) (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal) :
    σ.restrictNormal F = 1 ↔ v.asIdeal.inertiaDeg' (Q.under (𝓞 F)).asIdeal = 1 := by

  set w₀ : HeightOneSpectrum (𝓞 F) := Q.under (𝓞 F) with hw₀def
  have hw₀ : w₀.under (𝓞 E) = v := by
    ext1
    simp only [hw₀def, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    rw [← hQ]; rfl
  haveI : w₀.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw₀]; rfl⟩
  haveI : w₀.asIdeal.IsMaximal := w₀.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal

  have hσF : IsArithFrobAt (𝓞 E) (σ.restrictNormal F) w₀.asIdeal :=
    isArithFrobAt_restrictNormal F Q.asIdeal σ hσ
  rw [← isArithFrobAt_one_iff F v.asIdeal w₀.asIdeal]
  constructor
  · intro h
    rwa [h] at hσF
  · intro h1

    have hmem := hσF.mul_inv_mem_inertia h1
    rw [inertia_eq_bot F v hv w₀ hw₀, Subgroup.mem_bot] at hmem
    simpa using hmem

theorem inertiaDeg_le_finrank [IsGalois E F] (v : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    v.asIdeal.inertiaDeg' w.asIdeal ≤ Module.finrank E F := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hid := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 F)
    (F ≃ₐ[E] F)
  haveI := w.isMaximal
  rw [IsGaloisGroup.card_eq_finrank (F ≃ₐ[E] F) E F,
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (F ≃ₐ[E] F),
    ← Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal] at hid
  rw [← hid]
  have hg : (v.asIdeal.primesOver (𝓞 F)).ncard ≠ 0 :=
    IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 F)
  have he : v.asIdeal.ramificationIdxIn (𝓞 F) ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (F ≃ₐ[E] F)
  calc v.asIdeal.inertiaDeg' w.asIdeal
      = 1 * (1 * v.asIdeal.inertiaDeg' w.asIdeal) := by ring
    _ ≤ (v.asIdeal.primesOver (𝓞 F)).ncard *
          (v.asIdeal.ramificationIdxIn (𝓞 F) * v.asIdeal.inertiaDeg' w.asIdeal) := by
        gcongr <;> omega

theorem finrank_fixedField_eq_index [IsGalois E L] (N : Subgroup (L ≃ₐ[E] L)) :
    Module.finrank E (IntermediateField.fixedField N) = N.index := by
  have h1 := IntermediateField.finrank_fixedField_eq_card N
  have h2 := Module.finrank_mul_finrank E (IntermediateField.fixedField N) L
  have h3 := IsGalois.card_aut_eq_finrank E L
  have h4 := N.index_mul_card
  rw [h1, ← h3, ← h4] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

theorem index_ker_le_two {G : Type*} [Group G] (f : G →* ℤˣ) : f.ker.index ≤ 2 := by
  rw [Subgroup.index_ker]
  calc Nat.card f.range ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by simp

end SignFixedFieldFrobenius

open SignFixedFieldFrobenius in
open scoped Classical in
theorem solution
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : Type) [Field K] [NumberField K] [Algebra E K] [Algebra K L] [IsScalarTower E K L] :
    let H : Subgroup (L ≃ₐ[E] L) := (IsScalarTower.toAlgHom E K L).fieldRange.fixingSubgroup
    let ε : (L ≃ₐ[E] L) →* ℤˣ :=
      (Equiv.Perm.sign : Equiv.Perm ((L ≃ₐ[E] L) ⧸ H) →* ℤˣ).comp (MulAction.toPermHom (L ≃ₐ[E] L) ((L ≃ₐ[E] L) ⧸ H))
    let F : IntermediateField E L := IntermediateField.fixedField ε.ker
    Module.finrank E F ≤ 2 ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)), Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 →
        ∀ (Q : HeightOneSpectrum (𝓞 L)), Q.under (𝓞 E) = v →
          ∀ (σ : L ≃ₐ[E] L), IsArithFrobAt (𝓞 E) σ Q.asIdeal →
            ∀ w ∈ primeFibre E F v,
              (v.asIdeal.inertiaDeg' w.asIdeal = 1 ↔ ε σ = 1) ∧ (v.asIdeal.inertiaDeg' w.asIdeal = 2 ↔ ε σ = -1) := by
  intro H ε F

  haveI hFgal : IsGalois E F := IsGalois.of_fixedField_normal_subgroup ε.ker
  have hfin : Module.finrank E F ≤ 2 :=
    (finrank_fixedField_eq_index (E := E) (L := L) ε.ker).trans_le (index_ker_le_two ε)
  refine ⟨hfin, ?_⟩
  intro v hv Q hQ σ hσ w hw
  have hw' : w.under (𝓞 E) = v := (mem_primeFibre E v w).1 hw
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  haveI : (Q.under (𝓞 F)).asIdeal.LiesOver v.asIdeal := ⟨by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_under, ← hQ]; rfl⟩

  have key : v.asIdeal.inertiaDeg' w.asIdeal = 1 ↔ ε σ = 1 := by
    haveI := w.isMaximal
    haveI := (Q.under (𝓞 F)).isMaximal
    rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal,
      Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.asIdeal (Q.under (𝓞 F)).asIdeal
      (F ≃ₐ[E] F), ← Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal (Q.under (𝓞 F)).asIdeal,
      ← restrictNormal_eq_one_iff_inertiaDeg_under_eq_one F v hv Q hQ σ hσ,
      AlgEquiv.restrictNormal_eq_one_iff, ← IntermediateField.mem_fixingSubgroup_iff,
      show F = IntermediateField.fixedField ε.ker from rfl,
      IntermediateField.fixingSubgroup_fixedField, MonoidHom.mem_ker]
  refine ⟨key, ?_⟩

  have hle : v.asIdeal.inertiaDeg' w.asIdeal ≤ 2 := (inertiaDeg_le_finrank F v w hw').trans hfin
  have hpos : v.asIdeal.inertiaDeg' w.asIdeal ≠ 0 := Ideal.inertiaDeg_ne_zero _ _
  constructor
  · intro h2
    rcases Int.units_eq_one_or (ε σ) with h | h
    · rw [← key] at h; omega
    · exact h
  · intro hneg
    have hne : ¬ v.asIdeal.inertiaDeg' w.asIdeal = 1 := by
      rw [key, hneg]; decide
    omega

end S_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt
end P2MW
export P2MW.S_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt (solution)
