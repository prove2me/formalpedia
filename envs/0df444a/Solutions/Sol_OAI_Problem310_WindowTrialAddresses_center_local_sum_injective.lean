-- Prove2me | solution 1 for OAI.Problem310.WindowTrialAddresses.center_local_sum_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:30:05.507609+00:00
-- url     : https://prove2.me/submissions/8f7726ee-d700-45f0-b45e-f589147ff7c0

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowTrialAddresses.lean:L65-L85
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowTrialAddresses.center_local_sum_injective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_ne_of_separated
import Theorems.Thm_OAI_Problem310_TrialAddresses_trialAddress_injective

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

lemma periodicKey_ne_of_small_shift {q x d : ℝ} (hq : 4 ≤ q)
    (hlo : 1 ≤ q * d) (hhi : d ≤ 1 / 4) :
    periodicKey q x ≠ periodicKey q (x + d) := by
  apply periodicKey_ne_of_separated (by linarith)
  · simpa using hlo
  · have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ q by linarith)
    have : q * d ≤ q - 1 := by nlinarith
    simpa using this

lemma mesh_mul_dyadic (b : ℕ) :
    (2 : ℝ) ^ (b + 2) * (2 : ℝ)⁻¹ ^ b = 4 := by
  rw [pow_add, inv_pow]
  have hb : (2 : ℝ) ^ b ≠ 0 := by positivity
  field_simp
  ring

lemma mesh_ge_four (b : ℕ) : 4 ≤ (2 : ℝ) ^ (b + 2) := by
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  nlinarith

lemma dyadic_shift_le_quarter {n : ℕ} {t : ℝ} (hn : 3 ≤ n)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) : t * (2 : ℝ)⁻¹ ^ n ≤ 1 / 4 := by
  have hp : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  norm_num at hp
  have hnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  nlinarith

lemma mesh_mul_shift_ge_four {b n : ℕ} {t : ℝ}
    (hn : n ≤ b) (ht : 1 ≤ t) :
    4 ≤ (2 : ℝ) ^ (b + 2) * (t * (2 : ℝ)⁻¹ ^ n) := by
  have hp : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hpos : 0 < (2 : ℝ) ^ (b + 2) := by positivity
  have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hshift : (2 : ℝ)⁻¹ ^ b ≤ t * (2 : ℝ)⁻¹ ^ n := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hshift hpos.le
  rw [mesh_mul_dyadic] at hmul
  exact hmul

/-- Every tested dyadic translate uses a key different from the center's key. -/
lemma periodicKey_dyadic_ne_center {b n : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnhi : n ≤ b) (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n) := by
  apply periodicKey_ne_of_small_shift (mesh_ge_four b)
  · have := mesh_mul_shift_ge_four hnhi htlo
    linarith
  · exact dyadic_shift_le_quarter hnlo htlo hthi

lemma dyadicKey_ne_center {b n : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnhi : n ≤ b) (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    dyadicKey b x ≠ dyadicKey b (x + t * (2 : ℝ)⁻¹ ^ n) := by
  rw [ne_eq, dyadicKey_eq_iff]
  exact periodicKey_dyadic_ne_center hnlo hnhi htlo hthi

end Problem310.GridSeparation

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowTableModel ----
namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

variable {M d g r₀ : ℕ}

lemma selectorEdge_valid (P : Node M d) (i : Fin M) :
    ValidWindowEdge d (selectorEdge P i) := by
  constructor
  · simp [selectorEdge]
  · have hP := P.property
    simp only [selectorEdge, List.length_append, List.length_singleton]
    omega

lemma selector_window_endpoint
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) :
    selectorEndpoints W P i + 1 = W.a (selectorEdge P i) + W.r (d - P.val.length) := by
  have h := W.endpoint (selectorEdge P i) (selectorEdge_valid P i)
  simpa [selectorEndpoints, selectorEdge] using h

end Problem310.FiniteTableModel

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.TrialAddresses ----
namespace OAI

universe u_E u_I u_C u_L

noncomputable section

namespace Problem310.TrialAddresses

open GridSeparation

/-- A tested coordinate is distinct from every center-exposed coordinate. -/
theorem trialAddress_ne_center {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i)) (i : I) (e : E) :
    trialAddress b edge n x t i ≠ centerAddress b x e := by
  intro h
  have he : edge i = e := congrArg Sigma.fst h
  subst e
  have hv := congrArg (fun z : GridAddress b => z.2.val) h
  have hk : dyadicKey (b (edge i)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (b (edge i)) x := Fin.ext hv
  exact (dyadicKey_ne_center (hnlo i) (hnhi i) htlo hthi) hk.symm

theorem windowTrial_pair_injective {M r : ℕ} {E : Type u_E}
    (a : Fin M → ℕ) (edge : Fin M → E) (hedge : Function.Injective edge) :
    Function.Injective (fun i : WindowTrial M r =>
      (edge i.1, windowTrialIndex a i)) := by
  intro i j h
  have hc : i.1 = j.1 := hedge (congrArg Prod.fst h)
  have hn : windowTrialIndex a i = windowTrialIndex a j := congrArg Prod.snd h
  have ho : i.2 = j.2 := by
    apply Fin.ext
    dsimp [windowTrialIndex] at hn
    rw [hc] at hn
    omega
  exact Prod.ext hc ho

end Problem310.TrialAddresses

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowTrialAddresses ----
namespace OAI

noncomputable section

namespace Problem310.WindowTrialAddresses

open FiniteTableModel TrialAddresses

variable {M d g r₀ : ℕ}

theorem localIndex_bounds (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (z : LocalTrial W P) :
    3 ≤ localIndex W P z ∧ localIndex W P z ≤ selectorEndpoints W P z.1 := by
  have hs := W.start_three (selectorEdge P z.1) (selectorEdge_valid P z.1)
  have he := selector_window_endpoint W P z.1
  have hk := z.2.isLt
  dsimp [localIndex, windowTrialIndex, localStarts]
  omega

theorem localSelectorAddress_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (localSelectorAddress W P x t) := by
  change Function.Injective (trialAddress
    (fun e : Node M d × Fin M => selectorEndpoints W e.1 e.2)
    (fun z : LocalTrial W P => (P, z.1)) (localIndex W P) x t)
  apply trialAddress_injective _ _ _ _ _ ht.1 ht.2
  · exact fun z => (localIndex_bounds W P z).1
  · exact fun z => (localIndex_bounds W P z).2
  · exact windowTrial_pair_injective (localStarts W P) (fun i => (P, i))
      (fun _ _ h => congrArg Prod.snd h)

theorem localSelectorAddress_ne_center (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (z : LocalTrial W P) (e : Node M d × Fin M) :
    localSelectorAddress W P x t z ≠
      selectorAddress (selectorEndpoints W) e.1 e.2 x := by
  exact trialAddress_ne_center
    (fun e : Node M d × Fin M => selectorEndpoints W e.1 e.2)
    (fun z : LocalTrial W P => (P, z.1)) (localIndex W P) x t ht.1 ht.2
    (fun z => (localIndex_bounds W P z).1)
    (fun z => (localIndex_bounds W P z).2) z e

/-- This is the single address-injectivity assumption needed by center
exposure: every center coordinate and every local trial coordinate are fresh. -/
theorem center_local_sum_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (Sum.elim
      (fun e : Node M d × Fin M => selectorAddress (selectorEndpoints W) e.1 e.2 x)
      (localSelectorAddress W P x t)) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrArg Sum.inl (center_selectorAddress_injective (selectorEndpoints W) x h)
    | inr j =>
      exact False.elim ((localSelectorAddress_ne_center W P x t ht j i) h.symm)
  | inr i =>
    cases j with
    | inl j =>
      exact False.elim ((localSelectorAddress_ne_center W P x t ht i j) h)
    | inr j =>
      exact congrArg Sum.inr (localSelectorAddress_injective W P x t ht h)

end Problem310.WindowTrialAddresses

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowTrialAddresses
open FiniteTableModel TrialAddresses


theorem solution : type_of% @_root_.OAI.Problem310.WindowTrialAddresses.center_local_sum_injective := @_root_.OAI.Problem310.WindowTrialAddresses.center_local_sum_injective
