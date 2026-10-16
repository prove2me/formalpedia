-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.fine_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:17:56.086485+00:00
-- url     : https://prove2.me/submissions/7a38eea2-a854-4a9a-b78a-79f230bae330

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean:L144-L165
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.fine_parameters. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction

-- ---- from OAI.Combinatorics.TreeEdit.CircleTree ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma period_pos {I : Type} {g : ℕ} {r : I → ℕ} (hr : ∀ i, 0 < r i)
    (j : Fin g → I) (σ : Equiv.Perm I) : 0 < period r j σ := product_positive _ (fun _ => hr _)

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleObstruction ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

lemma allPeriods_pos {k : ℕ} (j : Fin (16*k) ↪ Pool k) : 0 < allPeriods j :=
  product_positive _ (fun σ => period_pos (fun p => (pool_properties p).1.pos) j σ)

lemma fine_parameters {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k) :
    0 < fineModulus j ∧ 2 ∣ fineModulus j ∧
    (∀ σ : Equiv.Perm (Pool k), period poolPrime j σ ∣ fineModulus j) ∧
    (branching k+1)*cutoff k < fineModulus j ∧
    ∃ D J : ℕ, 0 < D ∧ fineModulus j = resolution k*D ∧ fineModulus j = J*cutoff k := by
  have hR : 0 < resolution k := pow_pos (by omega) _
  have hQ : 0 < cutoff k := pow_pos (by omega) _
  have hP := allPeriods_pos j
  have hM : 0 < fineModulus j := by unfold fineModulus; positivity
  refine ⟨hM, ?_, ?_, ?_, ?_⟩
  · unfold fineModulus
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _) _) _
  · intro σ
    have hd : period poolPrime j σ ∣ allPeriods j := Finset.dvd_prod_of_mem _ (Finset.mem_univ σ)
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hd _) _
  · have he : fineModulus j = ((branching k+1)*cutoff k+1) * (resolution k*2*cutoff k*allPeriods j) := by unfold fineModulus; ring
    rw [he]
    have hh : 0 < resolution k*2*cutoff k*allPeriods j := by positivity
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hh)
  · refine ⟨2*cutoff k*((branching k+1)*cutoff k+1)*allPeriods j,
      resolution k*2*((branching k+1)*cutoff k+1)*allPeriods j, by positivity, rfl, ?_⟩
    unfold fineModulus; ring

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.fine_parameters := @_root_.OAI.TreeEdit.TorusTree.fine_parameters
