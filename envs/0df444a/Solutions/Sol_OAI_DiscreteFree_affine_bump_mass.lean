-- Prove2me | solution 1 for OAI.DiscreteFree.affine_bump_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:45:50.160243+00:00
-- url     : https://prove2.me/submissions/76fa122e-6cf0-4a28-8f45-3376cef64f82

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/LabelBumps.lean:L73-L107
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.affine_bump_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Theorems.Thm_OAI_DiscreteFree_affineWeights_pairing
import Theorems.Thm_OAI_DiscreteFree_labelBump_sub

-- ---- from OAI.Analysis.LipschitzFree.Coordinates ----
namespace OAI

/-!
# Signed evaluation coefficients and finite-support projections
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

theorem dualPairing_bound (f : Lip0 o) (u : FreeSpace o) : |dualPairing o f u| ≤ ‖u‖ * ‖f‖ :=
  u.val.le_opNorm f

namespace Lip0
theorem center_norm_le (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) : ‖center o g L hL hg‖ ≤ L := by
  apply (norm_le_iff _ hL).mpr
  intro x y
  simpa using hg x y
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.LabelBumps ----
namespace OAI

/-!
# Lipschitz label bumps and affine mass estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

omit [MetricSpace M] in
theorem labelBump_self (h : M → N) (a : N) {L K : ℝ} {t : M} (ht : h t = a) :
    labelBump h a L K t = L := by simp [labelBump, ht]

theorem affine_bump_mass (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)
    (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (h : M → N) (hh : LipschitzWith 1 h) (x a : M) (ha : h a = h x)
    (L K p R : ℝ) (hL : 0 ≤ L) (hK : 0 < K) (hp : 0 ≤ p)
    (hn : ‖T‖ ≤ 2*p) (hR : dist x a ≤ R) (he : ‖T (delta o a) - delta o a‖ < 1) :
    L - (L/K)*(2*p*R+1) ≤
      pairing (affineWeights o sep S ho (T (delta o x)))
        (fun j : S => labelBump h (h x) L K j.val) := by
  let b := labelBump h (h x) L K
  have hb (s t : M) : |b s - b t| ≤ (L/K)*dist s t := labelBump_sub h hh (h x) hL hK s t
  let f := Lip0.center o b (L/K) (div_nonneg hL hK.le) hb
  have hfn : ‖f‖ ≤ L/K := Lip0.center_norm_le o b _ _ hb
  have hda : ‖T (delta o x) - delta o a‖ ≤ 2*p*R+1 := by
    calc
      _ = ‖T (delta o x - delta o a) + (T (delta o a) - delta o a)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖T (delta o x - delta o a)‖ + ‖T (delta o a) - delta o a‖ := norm_add_le _ _
      _ ≤ (2*p)*R + 1 := add_le_add
        ((T.le_opNorm _).trans (mul_le_mul hn (by simpa using hR) (norm_nonneg _) (by positivity))) he.le
  have heq := affineWeights_pairing o sep S ho (T (delta o x)) (hfixed _) b (L/K)
    (div_nonneg hL hK.le) hb
  have hba : b a = L := labelBump_self h (h x) ha
  have hpair : pairing (affineWeights o sep S ho (T (delta o x))) (fun j : S => b j.val) - L =
      dualPairing o f (T (delta o x) - delta o a) := by
    rw [heq, map_sub, dualPairing_delta]
    change _ = _ - (b a - b o)
    rw [hba]
    ring
  have heval := (dualPairing_bound o f (T (delta o x) - delta o a)).trans
    (mul_le_mul hda hfn (norm_nonneg _) ((norm_nonneg _).trans hda))
  rw [← hpair] at heval
  have hh := (abs_le.mp heval).1
  change L - _ ≤ pairing _ (fun j : S => b j.val)
  nlinarith

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.affine_bump_mass := @_root_.OAI.DiscreteFree.affine_bump_mass
