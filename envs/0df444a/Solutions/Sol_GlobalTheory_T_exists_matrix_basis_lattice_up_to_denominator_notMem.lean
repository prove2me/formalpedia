-- Prove2me | solution 1 for GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:21:18.79429+00:00
-- url     : https://prove2.me/submissions/872a7872-6dd3-4a05-97f4-8436e78b4731

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMatrixBasisLatticeUpToDenominatorNotMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMatrixBasisLatticeUpToDenominatorNotMemStatement
import Theorems.Thm_GlobalTheory_LatticeLocBasis_exists_matrix_up_to_notMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  first | exact @GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | exact GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | (intros; apply GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem <;> assumption)
end _root_.GlobalTheory.T
