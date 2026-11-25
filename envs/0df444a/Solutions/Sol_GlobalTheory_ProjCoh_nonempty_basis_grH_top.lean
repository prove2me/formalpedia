-- Prove2me | solution 1 for GlobalTheory.ProjCoh.nonempty_basis_grH_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:14.984541+00:00
-- url     : https://prove2.me/submissions/6f875e7f-2bff-43ac-8251-712b078b507f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
import Theorems.Thm_GlobalTheory_ProjCoh_exists_basis_top
import Theorems.Thm_GlobalTheory_exists_basis_grCube_polyGrading


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
variable (R : Type) [CommRing R] (N : ℕ) (n : ℤ)
namespace GlobalTheory.ProjCoh
theorem _root_.solution (hN : 1 ≤ N) :
    Nonempty (Module.Basis (NegExp N n) R (grH (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n N)) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := N) (by omega)
  obtain ⟨b, hb⟩ := exists_basis_grCube_polyGrading (Fin (N + 1 + 1)) R n
  obtain ⟨c, -⟩ := exists_basis_top _ _ b hb (N := N) (Fintype.card_fin _)
  exact ⟨c.reindex
    { toFun := fun a => ⟨a.1.1, a.1.2, fun i => Finset.filter_eq_self.1 a.2 i (Finset.mem_univ i)⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, Finset.filter_eq_self.2 fun i _ => a.2.2 i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }⟩
end GlobalTheory.ProjCoh
