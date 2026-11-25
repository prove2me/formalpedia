-- Prove2me | solution 1 for GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:05.526629+00:00
-- url     : https://prove2.me/submissions/6aa4d06e-5264-475c-b88b-f6a9aa4bd8fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticZmodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSymplecticBasisCongrLevelMod
import Theorems.Thm_GlobalTheory_SymplecticLevelLift_omegaStd_single
import Theorems.Thm_GlobalTheory_SymplecticLevelLift_gram_eq
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_basis_of_toMatrix_mem
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_of_finrank
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_symplectic_zmod_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymplecticLevelLift
open Matrix Module
namespace GlobalTheory.SymplecticLevelLift
theorem _root_.solution : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by
  intro h k M _ _ _ Ef l _ hrk halt hbij hl
  have hE : Ef.IsAlt := halt
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hE hbij hrk
  set v : Fin h ⊕ Fin h → M := fun j => l (Pi.single j 1) with hv
  have hmem : (b.toMatrix v).map (Int.castRingHom (ZMod k)) ∈
      Matrix.symplecticGroup (Fin h) (ZMod k) := by
    rw [SymplecticGroup.mem_iff']
    have h1 : (Matrix.of fun i j => Ef (v i) (v j)).map (Int.castRingHom (ZMod k)) =
        (-Matrix.J (Fin h) ℤ).map (Int.castRingHom (ZMod k)) := by
      ext i j
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).2 (hl (Pi.single i 1) (Pi.single j 1))
      rw [omegaStd_single, Int.cast_sub, sub_eq_zero] at this
      simpa [hv] using this
    rw [gram_eq hb hE, Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (map_neg _), map_J,
      transpose_map] at h1
    simpa using h1
  obtain ⟨N, hN, hNT⟩ := symplectic_zmod_lift h k _ hmem
  have hw : b.toMatrix (fun j => ∑ i, N i j • b i) = N := by
    ext i j
    rw [Basis.toMatrix_apply, b.repr_sum_self]
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hE (hw.symm ▸ hN)
  have hcong : ∀ j, ∃ m : M, v j - c j = (k : ℤ) • m := by
    intro j
    have hd : ∀ i, ∃ t : ℤ, b.toMatrix v i j - N i j = k * t := fun i => by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).1 ?_
      have := congrFun (congrFun hNT i) j
      simp only [Matrix.map_apply, eq_intCast] at this
      rw [Int.cast_sub, this, sub_self]
    choose t ht using hd
    refine ⟨∑ i, t i • b i, ?_⟩
    rw [← b.sum_toMatrix_smul_self v j, hcv, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← sub_smul, ht, mul_smul]
  choose m hm using hcong
  refine ⟨c.equivFun.symm, fun x y => ?_, fun a => ⟨∑ j, a j • m j, ?_⟩⟩
  · have hr : ∀ (z : Fin h ⊕ Fin h → ℤ) i, c.repr (c.equivFun.symm z) i = z i := fun z i => by
      rw [← c.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hc.apply_eq_sum hE]
    simp only [hr, omegaStd]
  · have hla : l a = ∑ j, a j • v j := by
      conv_lhs => rw [← Finset.univ_sum_single a]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hv, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hla, c.equivFun_symm_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← smul_sub, hm, smul_comm]
end GlobalTheory.SymplecticLevelLift
