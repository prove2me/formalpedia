-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteDistribution.js_le_map_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:17:15.474068+00:00
-- url     : https://prove2.me/submissions/f23534c2-3c6b-422d-8f0a-332c3c216695

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean:L21-L33
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteDistribution.js_le_map_add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem negMulLog_sum_le {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  have hterm : ∀ i ∈ s,
      -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonpos_left
        (Real.log_le_log h (Finset.single_le_sum hp hi)) (neg_nonpos.mpr (hp i hi))
  have heq : (∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j)) =
      Real.negMulLog (∑ i ∈ s, p i) := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rfl
  rw [← heq]
  exact Finset.sum_le_sum hterm

theorem observableEntropy_le {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ entropy s p := by
  classical
  calc
    observableEntropy s p f ≤
        ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), Real.negMulLog (p a) := by
      apply Finset.sum_le_sum
      intro b _
      exact negMulLog_sum_le _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = entropy s p :=
      Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

theorem mass_subset {α : Type uα} {β : Type uβ} [DecidableEq β] {s t : Finset α}
    (p : α → ℝ) (f : α → β) (hst : s ⊆ t)
    (hp : ∀ x ∈ t, x ∉ s → p x = 0) (b : β) : mass s p f b = mass t p f b := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hst)
  intro x hx hn
  exact hp x (Finset.mem_filter.mp hx).1 (fun hs => hn (Finset.mem_filter.mpr ⟨hs,(Finset.mem_filter.mp hx).2⟩))

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteDistribution ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem entropy_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : p.entropy=FiniteEntropy.entropy s p.weight := by
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hs h)), Real.negMulLog_zero]

theorem map_weight_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) (b : β) :
    (p.map f).weight b=FiniteEntropy.mass s p.weight f b := by
  classical
  exact FiniteEntropy.mass_subset p.weight f hs (fun a _ ha => p.vanish a ha) b

theorem entropy_map_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) :
    (p.map f).entropy=FiniteEntropy.observableEntropy s p.weight f := by
  classical
  rw [(p.map f).entropy_on (s.image f) (Finset.image_subset_image hs)]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (p.map_weight_on f s hs b))

theorem mix_map_entropy {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
    ((p.map f).mix (q.map f)).entropy=
      FiniteEntropy.observableEntropy s (fun a => (p.weight a+q.weight a)/2) f := by
  classical
  rw [((p.map f).mix (q.map f)).entropy_on (s.image f)
    (Finset.union_subset (Finset.image_subset_image hp) (Finset.image_subset_image hq))]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change ((p.map f).weight b+(q.map f).weight b)/2=_
  rw [p.map_weight_on f s hp, q.map_weight_on f s hq]
  simp only [FiniteEntropy.mass, ← Finset.sum_div, Finset.sum_add_distrib]

end FiniteDistribution

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RandomGrid ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem entropy_map_le {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β) :
    (p.map f).entropy ≤ p.entropy := by
  classical
  rw [p.entropy_map_on f p.support (fun _ h => h),p.entropy_on p.support (fun _ h => h)]
  exact FiniteEntropy.observableEntropy_le _ _ _ (fun a _ => p.nonneg a)

theorem js_le_map_add {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    p.js q ≤ (p.map f).js (q.map f)+(p.mix q).entropy-((p.mix q).map f).entropy := by
  classical
  have he : ((p.map f).mix (q.map f)).entropy=((p.mix q).map f).entropy := by
    let s := p.support ∪ q.support
    rw [mix_map_entropy p q f s Finset.subset_union_left Finset.subset_union_right,
      (p.mix q).entropy_map_on f s (by exact fun _ h => h)]
    rfl
  have hp := p.entropy_map_le f
  have hq := q.entropy_map_le f
  unfold js
  rw [he]
  linarith

end FiniteDistribution
namespace RandomGrid

attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability
end RandomGrid

namespace MeasureEntropy

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteDistribution
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteDistribution.js_le_map_add.{uα,uβ} := @_root_.OAI.EntropyRateDimension.FiniteDistribution.js_le_map_add.{uα,uβ}
