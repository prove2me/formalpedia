-- Prove2me | solution 1 for OAI.MatchingEntropy.entropy_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:38:16.798633+00:00
-- url     : https://prove2.me/submissions/79fce31e-ce06-4ca6-b072-32ce6e7ba37d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Main.lean:L84-L130
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.MatchingEntropy.entropy_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_MatchingEntropy_entropy_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
import Theorems.Thm_OAI_MatchingEntropy_covariance_rank_bound
import Theorems.Thm_OAI_MatchingEntropy_entropyDefect_attains_max
import Theorems.Thm_OAI_MatchingEntropy_entropy_barrier_ge_id
import Theorems.Thm_OAI_MatchingEntropy_marginal_entropy_support_bound
import Theorems.Thm_OAI_MatchingEntropy_matching_covariance_rank
import Theorems.Thm_OAI_MatchingEntropy_matching_covariance_second_variation
import Theorems.Thm_OAI_MatchingEntropy_matching_covariance_trace

-- ---- from OAI.Combinatorics.PerfectMatching.Simplex ----
namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `Convexity.StdSimplex`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

theorem probabilitySimplex_le_one {Index : Type*} [Fintype Index] {weights : Index → ℝ}
    (mem : weights ∈ probabilitySimplex Index) (index : Index) : weights index ≤ 1 := by
  rw [← mem.2]
  exact Finset.single_le_sum (fun other _ ↦ mem.1 other) (Finset.mem_univ index)

theorem isCompact_probabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  exact isCompact_stdSimplex ℝ Index

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Basic ----
namespace OAI

/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem continuous_mean (G : LooplessGraph V E) : Continuous G.mean := by
  unfold mean
  fun_prop

omit [Fintype V] [DecidableEq V] in
theorem compact_feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) :
    IsCompact (G.feasibleLaws y) := by
  exact (isCompact_probabilitySimplex G.Matching).inter_right
    (isClosed_eq G.continuous_mean continuous_const)

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Entropy ----
namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem continuous_entropy {ι : Type*} [Fintype ι] :
    Continuous (entropy : (ι → ℝ) → ℝ) := by
  unfold entropy
  fun_prop

theorem entropy_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (hp.1 i)
    (probabilitySimplex_le_one hp i)

namespace LooplessGraph

end LooplessGraph

omit [Fintype V] [DecidableEq V] in
/-- The supremum in the definition of H is a genuine attained maximum. -/
theorem maxMatchingEntropy_attained (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    ∃ p ∈ G.feasibleLaws y, entropy p = maxMatchingEntropy G y := by
  have hc := (G.compact_feasibleLaws y).image continuous_entropy
  have hn := ((G.mem_polytope_iff y).mp hy).image entropy
  obtain ⟨p, hp, hpe⟩ := hc.sSup_mem hn
  exact ⟨p, hp, hpe⟩

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_nonneg (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) : 0 ≤ maxMatchingEntropy G y := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_nonneg hp.1

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Covariance ----
namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_posSemidef (p : A → ℝ) (b : A → I → ℝ) :
    (covariance p b).PosSemidef := by
  simpa only [covariance, conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (weightedColumns p b)

/-- The numerical contradiction following covariance rank and trace. -/
theorem covariance_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a m s : ℝ}
    (hm : 0 < m) (hs : 8*m < s) (hrank : s-4*m ≤ C.rank)
    (htrace : C.trace = s-m) (ha : 8*m/s ≤ a)
    (hsecond : ∀ u : ι → ℝ,
      (a-1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) : False := by
  have hb := covariance_rank_bound hC hsecond
  rw [htrace] at hb
  have hsp : 0 < s := by linarith
  have hsmp : 0 < s-m := by linarith
  have hau : a ≤ 3*m/(s-m) := by
    apply (le_div_iff₀ hsmp).mpr
    nlinarith
  have hcross := (div_le_div_iff₀ hsp hsmp).mp (ha.trans hau)
  nlinarith [mul_pos hm (show 0 < 5*s-8*m by linarith)]

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Main ----
namespace OAI

/-!
The nonlinear entropy defect bound
`F - H ≤ 8m (1 - exp (-F/m))` for finite loopless multigraphs on `2m` vertices,
and the perfect matching count bound `[k exp (-8 (1 - 1/k))]^m`,
with its coarse bound `(exp (-8) k)^m`, when the entire edge set
is partitioned into `k ≥ 1` perfect matchings.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Main entropy comparison, for every marginal in the actual matching polytope. -/
theorem entropy_main (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m)
    (hPM : Nonempty G.Matching) (y : E → ℝ) (hy : y ∈ G.polytope) :
    marginalEntropy y - maxMatchingEntropy G y ≤
      8 * (m : ℝ) * (1 - Real.exp (-marginalEntropy y / (m : ℝ))) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have heven : Even (Fintype.card V) := by rw [hV]; exact even_two_mul m
  obtain ⟨x,hx,hmax⟩ := entropyDefect_attains_max G heven hPM (m:ℝ)
  by_contra htarget
  have hypos : 0 < entropyDefect G (m:ℝ) y := by
    dsimp [entropyDefect,entropyBarrier,marginalEntropy] at *
    linarith
  have hpos : 0 < entropyDefect G (m:ℝ) x := hypos.trans_le (hmax y hy)
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨hxnon,hspos,hentropy⟩ := marginal_entropy_support_bound G hm hV hx
  have hH := maxMatchingEntropy_nonneg G hx
  let s : ℝ := Fintype.card {e // 0 < x e}
  have hsR : 0 < s := by dsimp only [s]; exact_mod_cast hspos
  have hrpos : 0 < s/(m:ℝ) := div_pos hsR hmR
  have hu : entropy x/(m:ℝ) ≤ Real.log (s/(m:ℝ)) := by
    apply (div_le_iff₀ hmR).mpr
    simpa only [mul_comm] using hentropy
  have hlo : Real.log 8 < entropy x/(m:ℝ) := by
    by_contra hle
    have hb := entropy_barrier_ge_id (div_nonneg hxnon hmR.le) (le_of_not_gt hle)
    have hb' := (div_le_iff₀ hmR).mp hb
    dsimp only [entropyDefect,entropyBarrier] at hpos
    rw [neg_div] at hpos
    nlinarith
  have hs8 : 8*(m:ℝ) < s := by
    have hh := (Real.log_lt_log_iff (by norm_num : (0:ℝ)<8) hrpos).mp (hlo.trans_le hu)
    exact (lt_div_iff₀ hmR).mp hh
  have ha : 8*(m:ℝ)/s ≤ 8*Real.exp (-entropy x/(m:ℝ)) := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg hu)
    rw [Real.exp_neg,Real.exp_log hrpos,inv_div] at hh
    rw [neg_div,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have hrankNat := matching_covariance_rank G heven hp hopt
  rw [hV] at hrankNat
  have hrankR : s ≤ 2*(2*(m:ℝ))+(covariance p (matchingNormalized G x)).rank := by
    dsimp only [s]
    exact_mod_cast hrankNat
  have hrank : s-4*(m:ℝ) ≤ (covariance p (matchingNormalized G x)).rank := by linarith
  exact covariance_contradiction (covariance_posSemidef p (matchingNormalized G x)) hmR hs8
    hrank (matching_covariance_trace G hp hV) ha
    (matching_covariance_second_variation G hp hopt hmR hmax)

end MatchingEntropy

end

end OAI

-- ---- mission target ----
open OAI OAI.MatchingEntropy
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
open scoped BigOperators Topology
open Filter
open Matrix

theorem solution (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m)
    (hPM : Nonempty G.Matching) (y : E → ℝ) (hy : y ∈ G.polytope) :
    marginalEntropy y - maxMatchingEntropy G y ≤
      8 * (m : ℝ) * (1 - Real.exp (-marginalEntropy y / (m : ℝ))) := by
  first
    | exact OAI.MatchingEntropy.entropy_main G m hm hV hPM y hy
    | exact OAI.MatchingEntropy.entropy_main
    | (apply OAI.MatchingEntropy.entropy_main <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropy_main <;> assumption)
