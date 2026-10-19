-- Prove2me | solution 1 for OAI.Problem313.block_conditional_low_degree_bound_of_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:37:14.12056+00:00
-- url     : https://prove2.me/submissions/219edeb9-c7bf-4130-a74c-8528e423e5f8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockLowDegree.lean:L90-L128
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.block_conditional_low_degree_bound_of_estimate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
import Theorems.Thm_OAI_Problem313_Reindex_influence_le_total_div
import Theorems.Thm_OAI_Problem313_RestrictionInfluence_average_influence
import Theorems.Thm_OAI_Problem313_exists_freeEdge_orbit_family
import Theorems.Thm_OAI_Problem313_permEdge_eq_self_of_not_touches

-- ---- from OAI.Combinatorics.SharpThreshold.InfluenceReindex ----
namespace OAI

universe u v

noncomputable section

namespace Problem313
namespace Reindex

variable {ι : Type u} {κ : Type v}

theorem config_update [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (x : ι → Bool) (i : ι) (b : Bool) :
    config e (Function.update x i b) = Function.update (config e x) (e i) b := by
  classical
  ext j
  by_cases h : j = e i
  · subst j; simp [config]
  · have h' : e.symm j ≠ i := by
      intro he
      apply h
      simpa using congrArg e he
    simp [config, h, h']

theorem weight_config [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (p : ℝ) (x : ι → Bool) : weight p (config e x) = weight p x := by
  unfold weight
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

theorem influence_config [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (p : ℝ) (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool)
    (hfg : ∀ x, g (config e x) = f x) (i : ι) :
    influence p g (e i) = influence p f i := by
  classical
  unfold influence
  apply Eq.symm
  apply Fintype.sum_equiv (configEquiv e)
  intro x
  simp only [configEquiv_apply, ← config_update, hfg, weight_config]

theorem weight_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ι → Bool) : 0 ≤ weight p x := by
  unfold weight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> linarith

end Reindex
end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BlockSymmetry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u v w

noncomputable section

namespace Problem313

/-- A permutation preserving the free coordinates and fixing all exterior coordinates
commutes with pasting, without changing the fixed exterior configuration. -/
theorem pasteCube_reindex {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i)
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) :
    (fun i => pasteCube P x y (π.symm i)) =
      pasteCube P (fun i => x ((π.subtypeEquiv hP).symm i)) y := by
  funext i
  by_cases hi : P i
  · have hi' : P (π.symm i) := (hP _).mpr (by simpa using hi)
    simp only [pasteCube, dite_eq_left hi, dite_eq_left hi']
    rfl
  · have hsi : π.symm i = i := (π.symm_apply_eq).mpr (hfix i hi).symm
    simp [pasteCube, hi, hsi]

/-- Coordinate symmetry survives conditioning outside a set when the symmetry
fixes every exterior coordinate individually. -/
theorem restrictCube_invariant {α : Type u} {β : Type v} {γ : Type w} (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i) (f : (α → β) → γ)
    (hf : ∀ z, f (fun i => z (π.symm i)) = f z)
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) :
    restrictCube P f y (fun i => x ((π.subtypeEquiv hP).symm i)) =
      restrictCube P f y x := by
  unfold restrictCube
  rw [← pasteCube_reindex P π hP hfix x y]
  exact hf _

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BlockInfluence ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Pivotal influences of a conditioned function are invariant under every
coordinate permutation that preserves the free set and fixes its complement. -/
theorem restrictCube_influence_reindex {α : Type u} [Fintype α]
    (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i) (f : (α → Bool) → Bool)
    (hf : ∀ z, f (fun i => z (π.symm i)) = f z)
    (p : ℝ) (y : {i // ¬ P i} → Bool) (i : {i // P i}) :
    Reindex.influence p (restrictCube P f y) ((π.subtypeEquiv hP) i) =
      Reindex.influence p (restrictCube P f y) i := by
  apply Reindex.influence_config (π.subtypeEquiv hP)
  intro x
  exact restrictCube_invariant P π hP hfix f hf x y

/-- Conditional edge influences respect vertex permutations supported on the block. -/
theorem restrictCube_influence_permEdge {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (π : Equiv.Perm (Fin n)) (hπ : SupportedOnBlock B π)
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p : ℝ) (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y)
        ⟨permEdge π e.val, (edgeTouches_permEdge_iff hπ e.val).mpr e.property⟩ =
      Reindex.influence p (restrictCube (EdgeTouches B) f y) e := by
  let hP : ∀ i, EdgeTouches B i ↔ EdgeTouches B ((permEdgeEquiv π) i) :=
    fun i => (edgeTouches_permEdge_iff hπ i).symm
  exact restrictCube_influence_reindex (EdgeTouches B) (permEdgeEquiv π) hP
    (fun i hi => permEdge_eq_self_of_not_touches hπ i hi) f (hf π) p y e

/-- Every conditional influence on edges touching a block is at most the total
conditional influence divided by the number of block vertices. -/
theorem block_restricted_influence_le {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (hB : 3 ≤ B.card)
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y) e ≤
      (∑ d, Reindex.influence p (restrictCube (EdgeTouches B) f y) d) /
        (B.card : ℝ) := by
  classical
  obtain ⟨S, hcard, horbit⟩ := exists_freeEdge_orbit_family B hB e
  have hm : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
  apply Reindex.influence_le_total_div hp0 hp1 _ e S hm (by exact_mod_cast hcard)
  intro d hd
  obtain ⟨π, hπ, hmap⟩ := horbit d hd
  simpa only [hmap] using restrictCube_influence_permEdge B π hπ f hf p y e

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.RestrictionInfluence ----
namespace OAI

universe u

/-! Finite-product averaging for pivotal influences under restrictions. -/
noncomputable section
open scoped BigOperators

namespace Problem313.RestrictionInfluence

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

variable (P : ι → Prop) [DecidablePred P]

/-- Averaging total influence on the free coordinates gives the sum of their original influences. -/
theorem average_totalInfluence (p : ℝ) (f : (ι → Bool) → Bool) :
    (∑ y : {i // ¬ P i} → Bool, weight p y *
      ∑ i : {i // P i}, influence p (fun x => f (join P x y)) i) =
        ∑ i : {i // P i}, influence p f i.val := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => average_influence P p f i)

end Problem313.RestrictionInfluence

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphRestrictionInfluence ----
namespace OAI

universe u

noncomputable section
open scoped Classical BigOperators

namespace Problem313

/-- The generic restriction influence agrees with the qualified graph influence. -/
theorem restrictionInfluence_eq_edgeInfluence {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool) (e : GraphEdge n) :
    RestrictionInfluence.influence p f e = edgeInfluence p f e := rfl

/-- The two generic influence interfaces have definitionally identical weights. -/
theorem restrictionWeight_eq_reindexWeight {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (x : ι → Bool) :
    RestrictionInfluence.weight p x = Reindex.weight p x := rfl

/-- The two generic influence interfaces have equal influences after identifying their decidable-equality instances. -/
theorem restrictionInfluence_eq_reindexInfluence {ι : Type u} [Fintype ι] [d : DecidableEq ι]
    (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    RestrictionInfluence.influence p f i = Reindex.influence p f i := by
  cases Subsingleton.elim d (Classical.typeDecidableEq ι)
  rfl

/-- Averaging conditional total influence gives precisely the original influences of
edges touching the block; no invariance or monotonicity is needed. -/
theorem block_average_totalInfluence {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (p : ℝ)
    (f : GraphConfig n → Bool) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      Reindex.weight p y * ∑ e : {e : GraphEdge n // EdgeTouches B e},
        Reindex.influence p (restrictCube (EdgeTouches B) f y) e) =
      ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have h := RestrictionInfluence.average_totalInfluence (EdgeTouches B) p f
  unfold RestrictionInfluence.join at h
  unfold restrictCube pasteCube
  simpa only [← restrictionWeight_eq_reindexWeight,
    ← restrictionInfluence_eq_reindexInfluence,
    ← restrictionInfluence_eq_edgeInfluence] using h

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BlockLowDegree ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators

namespace Problem313

/-- The conditional influence premise for the low-degree theorem follows from
vertex invariance and the low-degree estimate on the restricted cube. -/
theorem block_conditional_low_degree_bound_of_estimate
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p k C : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hestimate : ∀ g : ({e : GraphEdge n // EdgeTouches B e} → Bool) → Bool,
      (∀ e, Reindex.influence p g e ≤
        (∑ d, Reindex.influence p g d) / (B.card : ℝ)) →
      (∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p (fun x => boolReal (g x)) A ^ 2 else 0) ≤
      C * ∑ e, Reindex.influence p g e) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      BiasedFourier.weight p y *
        ∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
          if A.Nonempty ∧ (A.card : ℝ) ≤ k then
            BiasedFourier.coeff p
              (fun x => boolReal (restrictCube (EdgeTouches B) f y x)) A ^ 2
          else 0) ≤
      C * ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have hb (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool) :=
    hestimate (restrictCube (EdgeTouches B) f y)
      (fun e => block_restricted_influence_le B hB f hf hp hp1 y e)
  calc
    _ ≤ ∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
        Reindex.weight p y *
          (C * ∑ e, Reindex.influence p (restrictCube (EdgeTouches B) f y) e) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hb y) (Reindex.weight_nonneg hp hp1 y)
    _ = C * ∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
        Reindex.weight p y *
          ∑ e, Reindex.influence p (restrictCube (EdgeTouches B) f y) e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [block_average_totalInfluence]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem313.block_conditional_low_degree_bound_of_estimate := @_root_.OAI.Problem313.block_conditional_low_degree_bound_of_estimate
