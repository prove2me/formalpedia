-- Prove2me | solution 1 for ModularCurve.finiteDimensional_adjoin_jqModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fe580ae5-aec2-5e26-9624-1d63ee1bfe29

import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_adjoin_jqModC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

open IsLocalRing ModularCurve

private theorem adjoin_pair_subtype_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x y : L) :
    IntermediateField.adjoin K
        ({⟨x, IntermediateField.subset_adjoin K {x, y} (Set.mem_insert x {y})⟩,
          ⟨y, IntermediateField.subset_adjoin K {x, y} (Set.mem_insert_of_mem x rfl)⟩} :
          Set (IntermediateField.adjoin K ({x, y} : Set L))) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  induction hz using IntermediateField.adjoin_induction with
  | mem z hzm =>
    rcases hzm with rfl | hzm
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    · rcases hzm with rfl
      exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  | algebraMap a => exact IntermediateField.algebraMap_mem _ a
  | add a b ha hb hia hib => exact add_mem hia hib
  | mul a b ha hb hia hib => exact mul_mem hia hib
  | inv a ha hia => exact inv_mem hia

set_option maxHeartbeats 3200000 in
private theorem isIntegral_adjoin_of_isIntegral_adjoin_map
    {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M] [Algebra K L]
    (f : M →ₐ[K] L) (x y : M)
    (hL : IsIntegral (IntermediateField.adjoin K ({f x} : Set L)) (f y)) :
    IsIntegral (IntermediateField.adjoin K ({x} : Set M)) y := by
  classical
  obtain ⟨p, hpm, hpz⟩ := hL
  have hle2 : IntermediateField.adjoin K ({f x} : Set L) ≤ (IntermediateField.adjoin K ({x} : Set M)).map f := by
    refine IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ?_)
    exact ⟨x, IntermediateField.subset_adjoin K _ rfl, rfl⟩
  let θ : ↥(IntermediateField.adjoin K ({f x} : Set L)) →+* ↥(IntermediateField.adjoin K ({x} : Set M)) :=
    ((IntermediateField.equivMap (IntermediateField.adjoin K ({x} : Set M)) f).symm.toAlgHom.toRingHom).comp
      ((IntermediateField.inclusion hle2).toRingHom)
  have hθ : ∀ b : ↥(IntermediateField.adjoin K ({f x} : Set L)), f ((θ b : ↥(IntermediateField.adjoin K ({x} : Set M))) : M) = (b : L) := by
    intro b
    have h1 : f (((IntermediateField.equivMap (IntermediateField.adjoin K ({x} : Set M)) f).symm
        (IntermediateField.inclusion hle2 b) : ↥(IntermediateField.adjoin K ({x} : Set M))) : M)
        = ((IntermediateField.equivMap (IntermediateField.adjoin K ({x} : Set M)) f)
            ((IntermediateField.equivMap (IntermediateField.adjoin K ({x} : Set M)) f).symm
              (IntermediateField.inclusion hle2 b)) : L) :=
      (IntermediateField.coe_equivMap_apply _ _ _).symm
    rw [AlgEquiv.apply_symm_apply] at h1
    exact h1
  refine ⟨p.map θ, hpm.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  apply f.toRingHom.injective
  have h2 := Polynomial.hom_eval₂ p
    ((algebraMap ↥(IntermediateField.adjoin K ({x} : Set M)) M).comp θ) f.toRingHom y
  have hcomp : (f.toRingHom).comp ((algebraMap ↥(IntermediateField.adjoin K ({x} : Set M)) M).comp θ)
      = algebraMap ↥(IntermediateField.adjoin K ({f x} : Set L)) L :=
    RingHom.ext fun b => hθ b
  rw [map_zero]
  calc f.toRingHom (p.eval₂ ((algebraMap ↥(IntermediateField.adjoin K ({x} : Set M)) M).comp θ) y)
      = p.eval₂ ((f.toRingHom).comp ((algebraMap ↥(IntermediateField.adjoin K ({x} : Set M)) M).comp θ)) (f y) := h2
    _ = 0 := by rw [hcomp]; exact hpz

set_option maxHeartbeats 3200000 in
theorem solution
    {N : ℕ} [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    FiniteDimensional
      ↥(IntermediateField.adjoin (ResidueField A)
        ({((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) : ↥(modularFunctionFieldC (ResidueField A) N))} : Set ↥(modularFunctionFieldC (ResidueField A) N)))
      ↥(modularFunctionFieldC (ResidueField A) N) := by
  have hint : IsIntegral (IntermediateField.adjoin (ResidueField A) ({⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N)))
      (⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) :=
    isIntegral_adjoin_of_isIntegral_adjoin_map
      (modularFunctionFieldC (ResidueField A) N).val
      (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)
      (⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)
      (ModularCurve.isIntegral_jqNModC_all (ResidueField A) N)
  have htop := adjoin_pair_subtype_eq_top (K := (ResidueField A))
    (jqModC (ResidueField A)) (jqNModC (ResidueField A) N)
  have htower := IntermediateField.adjoin_adjoin_left (ResidueField A)
    ({⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N)) ({⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N))
  rw [Set.singleton_union] at htower
  have hpair : IntermediateField.adjoin (ResidueField A)
      ({⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩, ⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩} :
        Set (modularFunctionFieldC (ResidueField A) N)) = ⊤ := htop
  rw [hpair] at htower
  have hFD : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N)))
      (IntermediateField.adjoin (IntermediateField.adjoin (ResidueField A) ({⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N))) ({⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N))) :=
    IntermediateField.adjoin.finiteDimensional hint
  have h2 : IntermediateField.adjoin (IntermediateField.adjoin (ResidueField A) ({⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N))) ({⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N)) = ⊤ :=
    IntermediateField.restrictScalars_injective (ResidueField A)
      (htower.trans IntermediateField.restrictScalars_top.symm)
  rw [h2] at hFD
  exact (IntermediateField.topEquiv (F := IntermediateField.adjoin (ResidueField A) ({⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩} : Set (modularFunctionFieldC (ResidueField A) N)))).toLinearEquiv.finiteDimensional

#print axioms solution

end S_ModularCurve_finiteDimensional_adjoin_jqModC
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_adjoin_jqModC (solution)
