-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a154f1e8-ce5b-5080-b621-234223a90597

import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd
import Theorems.Thm_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
import Theorems.Thm_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul
import Theorems.Thm_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
import Theorems.Thm_ValuationSubring_tameCharacter_pow_sq_sub_one_eq_one_of_mem_inertiaSubgroupIn
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open scoped MatrixGroups

theorem RedNat.ofAlgAut_smul_place {K F : Type} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (P : AlgebraicCurve.Place K F) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • P = σ • P := by
  ext1
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, AlgebraicCurve.Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv]
  rfl

section Helpers

theorem RedNat.exists_mem_Gamma0_redQ_inv_smul_lineInfty_eq (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hqM' : ¬ q ∣ M') (ℓ : CuspidalType.ProjLine q) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      (ModularCurve.FullLevel.redQ q γ)⁻¹ • ModularCurve.FullLevel.lineInfty q = ℓ := by

  have key : ∃ g : SL(2, ZMod q), (Matrix.SpecialLinearGroup.toGL g : CuspidalType.GL2 q) • ℓ =
      ModularCurve.FullLevel.lineInfty q := by
    induction ℓ using Projectivization.ind with
    | h v hv =>
      by_cases ha : v 0 = 0
      · have hb : v 1 ≠ 0 := by
          intro hb; apply hv; ext i; fin_cases i <;> simp [ha, hb]
        refine ⟨⟨!![0, (v 1)⁻¹; -(v 1), 0], by rw [Matrix.det_fin_two_of, zero_mul, mul_neg, zero_sub, neg_neg, inv_mul_cancel₀ hb]⟩, ?_⟩
        rw [Projectivization.smul_mk]
        show Projectivization.mk (ZMod q) (Matrix.mulVec !![0, (v 1)⁻¹; -(v 1), 0] v) _ = _
        congr 1
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail, ha, hb, ModularCurve.FullLevel.lineInfty]
      · refine ⟨⟨!![(v 0)⁻¹, 0; -(v 1), v 0], by rw [Matrix.det_fin_two_of, zero_mul, sub_zero, inv_mul_cancel₀ ha]⟩, ?_⟩
        rw [Projectivization.smul_mk]
        show Projectivization.mk (ZMod q) (Matrix.mulVec !![(v 0)⁻¹, 0; -(v 1), v 0] v) _ = _
        congr 1
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail, ha, ModularCurve.FullLevel.lineInfty]; ring
  obtain ⟨g, hg⟩ := key
  obtain ⟨γ, hγ, hmap⟩ := (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').1 g
  refine ⟨γ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1
  · have : ModularCurve.FullLevel.redQ q γ = Matrix.SpecialLinearGroup.toGL g := by
      change Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ) = _
      rw [hmap]
    rw [this, inv_smul_eq_iff, hg]

theorem RedNat.exists_mem_Gamma0_diag_conj (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (d : (ZMod q)ˣ) (α : SL(2, ℤ)) :
    ∃ α' : SL(2, ℤ), α' ∈ CongruenceSubgroup.Gamma0 M' ∧
      !![(1 : ZMod q), 0; 0, (d : ZMod q)] * (α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
        = (α' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (d : ZMod q)] := by
  set D : Matrix (Fin 2) (Fin 2) (ZMod q) := !![(1 : ZMod q), 0; 0, (d : ZMod q)] with hD
  set D' : Matrix (Fin 2) (Fin 2) (ZMod q) := !![(1 : ZMod q), 0; 0, ((d⁻¹ : (ZMod q)ˣ) : ZMod q)] with hD'
  have hDD' : D' * D = 1 := by
    rw [hD, hD']
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit]
  set A : Matrix (Fin 2) (Fin 2) (ZMod q) := (α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) with hA
  have hAdet : A.det = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) α)
    simpa using this
  have hdet : (D * A * D').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hAdet, hD, hD', Matrix.det_fin_two_of, Matrix.det_fin_two_of]
    simp [-ZMod.inv_coe_unit]
  obtain ⟨α', hα', hmap⟩ := (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').1 ⟨D * A * D', hdet⟩
  refine ⟨α', ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hα').2.2.1
  · have h' : (α' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) = D * A * D' := by
      have := congrArg (fun g : SL(2, ZMod q) => (g : Matrix (Fin 2) (Fin 2) (ZMod q))) hmap
      simpa using this
    rw [h', Matrix.mul_assoc, Matrix.mul_assoc, hDD', Matrix.mul_one]

theorem RedNat.exists_unit_algebraMap_eq_pow_succ (q : ℕ) [Fact q.Prime] (α : (GaloisField q 2)ˣ) :
    ∃ d : (ZMod q)ˣ, algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) := by
  have hq : q.Prime := Fact.out
  set x : GaloisField q 2 := (α : GaloisField q 2) ^ (q + 1) with hx

  haveI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card q 2 (by norm_num)
  have hαpow : (α : GaloisField q 2) ^ (q ^ 2 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (α : GaloisField q 2) α.ne_zero
    rwa [hcard] at this
  have hxq : x ^ q = x := by
    rw [hx, ← pow_mul]
    have : (q + 1) * q = (q ^ 2 - 1) + (q + 1) := by
      have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
      zify [h1]; ring
    rw [this, pow_add, hαpow, one_mul]

  set f : Polynomial (ZMod q) := Polynomial.X ^ q - Polynomial.X with hf
  have hroots : f.roots = (Finset.univ : Finset (ZMod q)).val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod q)
    rwa [ZMod.card] at this
  have hdeg : f.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod q) hq.one_lt
  have hcardroots : f.roots.card = f.natDegree := by
    rw [hroots, hdeg]; simp [ZMod.card]
  have hmaproots := Polynomial.roots_map_of_injective_of_card_eq_natDegree (algebraMap (ZMod q) (GaloisField q 2)).injective hcardroots
  have hxroot : x ∈ (f.map (algebraMap (ZMod q) (GaloisField q 2))).roots := by
    rw [Polynomial.mem_roots', Polynomial.IsRoot]
    refine ⟨?_, ?_⟩
    · rw [hf, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
      exact FiniteField.X_pow_card_sub_X_ne_zero (GaloisField q 2) hq.one_lt
    · simp [hf, hxq]
  rw [← hmaproots, Multiset.mem_map] at hxroot
  obtain ⟨d₀, -, hd₀⟩ := hxroot
  have hd₀ne : d₀ ≠ 0 := by
    rintro rfl; rw [map_zero] at hd₀; exact pow_ne_zero _ α.ne_zero hd₀.symm
  exact ⟨Units.mk0 d₀ hd₀ne, by simpa using hd₀⟩

end Helpers

set_option maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (W : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField P)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField P) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ModularCurve.ssPlaces q M' (IsLocalRing.ResidueField P))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField P))]
    (hle : ModularCurve.modularFunctionFieldBar M' ≤ ModularCurve.FullLevel.fieldBar q M')
    (R₀ : AlgebraicCurve.ConstantReduction P ↥(ModularCurve.modularFunctionFieldBar M')
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField P) M'))

    (hR₀ : ∀ (y : LaurentSeries ↥P) (hy : ModularCurve.coeffMap P.subtype y ∈ ModularCurve.modularFunctionFieldBar M'),
      ∃ h : (⟨ModularCurve.coeffMap P.subtype y, hy⟩ : ↥(ModularCurve.modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField P) M') :
            LaurentSeries (IsLocalRing.ResidueField P)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥P) y) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses →
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) →
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →
      𝒞.InertiaIgusaInftyClause →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ ℓ : CuspidalType.ProjLine q, ∃ ℓ' : CuspidalType.ProjLine q,
        ∀ Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'), Q ∈ (𝒞.CIg ℓ).dom →
          ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ • Q ∈
            (𝒞.CIg ℓ').dom := by
  intro 𝒞 h1 hDr hIgU h3 h4 h5 h6 h7 h8 h9 hIg τ hτ ℓ

  obtain ⟨-, hdomI, -, -⟩ := hIg τ hτ

  obtain ⟨ζ₀, hd⟩ := h9.2.2.2

  obtain ⟨α₀, hα₀⟩ := (ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
    q P hP π hπ).2.2 ι τ
  have hq : q.Prime := Fact.out
  have hα₀ne : α₀ ≠ 0 := by
    intro h0
    have h1 := ValuationSubring.tameCharacter_pow_sq_sub_one_eq_one_of_mem_inertiaSubgroupIn q P hP π hπ τ hτ
    rw [← hα₀, h0, map_zero, zero_pow (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hq.one_lt))] at h1
    exact zero_ne_one h1
  obtain ⟨d, hdnorm⟩ := RedNat.exists_unit_algebraMap_eq_pow_succ q (Units.mk0 α₀ hα₀ne)
  have hlab : τ • ζ₀ = ζ₀.pow d :=
    ModularCurve.FullLevel.Idx.smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ q P hP π hπ ι hτ
      (Units.mk0 α₀ hα₀ne) hα₀ d hdnorm ζ₀

  obtain ⟨γ, hγ, hγℓ⟩ := RedNat.exists_mem_Gamma0_redQ_inv_smul_lineInfty_eq q M' hqM' ℓ
  have hdomℓ := (hd γ hγ (ModularCurve.FullLevel.lineInfty q)).2.1
  rw [hγℓ] at hdomℓ

  obtain ⟨γ', hγ', hconj⟩ := RedNat.exists_mem_Gamma0_diag_conj q M' hqM' d⁻¹ γ⁻¹
  have hL : ModularCurve.FullLevel.levelAutBar q M' (τ • ζ₀) γ⁻¹ = ModularCurve.FullLevel.levelAutBar q M' ζ₀ γ' := by
    rw [hlab]
    have := ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj q M' hqM' ζ₀ d⁻¹ γ⁻¹ γ'
      (inv_mem hγ) hγ' hconj
    rwa [inv_inv] at this

  have hgal := ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul q M' hqM' τ (τ • ζ₀) γ⁻¹
    (inv_mem hγ)
  rw [inv_smul_smul, hL] at hgal

  refine ⟨(ModularCurve.FullLevel.redQ q γ'⁻¹)⁻¹ • ModularCurve.FullLevel.lineInfty q, fun Q hQ => ?_⟩
  have h1' : Q ∈ ((𝒞.CIg (ModularCurve.FullLevel.lineInfty q)).comap
      (ModularCurve.FullLevel.levelAutBar q M' ζ₀ γ⁻¹)).dom := by
    rw [hdomℓ]; exact hQ
  rw [ComponentChart.mem_comap_dom, ← RedNat.ofAlgAut_smul_place] at h1'
  have h2' := (hdomI _).1 h1'
  rw [← mul_smul, hgal, mul_smul, RedNat.ofAlgAut_smul_place] at h2'
  have h3 := (hd γ'⁻¹ (inv_mem hγ') (ModularCurve.FullLevel.lineInfty q)).2.1
  rw [inv_inv] at h3
  rw [← h3, ComponentChart.mem_comap_dom]
  exact h2'

end S_ModularCurve_FullLevel_exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause_of_eq_two (solution)
