-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.exists_basis_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:41.849886+00:00
-- url     : https://prove2.me/submissions/148e6199-62f2-49f6-ac8b-eb70be02531d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
import Theorems.Thm_GlobalTheory_Mass_SameBad_ext_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
omit [NumberField K]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (β : K) (b : Module.Basis (Fin n) K V) :
    ∃ (j : ℕ) (c : Module.Basis (Fin j) K (V × K)), (Matrix.of fun i l => ext h β (c i) (c l)).det =
      (Matrix.of fun i l => h (b i) (b l)).det * β := by
  let c := b.prod (Module.Basis.singleton Unit K)
  let e := Fintype.equivFin (Fin n ⊕ Unit)
  refine ⟨_, c.reindex e, ?_⟩
  have e1 : (Matrix.of fun i l => ext h β (c.reindex e i) (c.reindex e l)) =
      (Matrix.fromBlocks (Matrix.of fun i l => h (b i) (b l)) 0 0
        (Matrix.of fun _ _ : Unit => β)).submatrix e.symm e.symm := by
    ext i l
    simp only [Module.Basis.reindex_apply, Matrix.of_apply, Matrix.submatrix_apply]
    generalize e.symm i = i'
    generalize e.symm l = l'
    rcases i' with i' | i' <;> rcases l' with l' | l' <;>
      simp [c, ext_apply, Module.Basis.prod_apply]
  rw [e1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp
end GlobalTheory.Mass.SameBad
