-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.avg_fibers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:20:38.285671+00:00
-- url     : https://prove2.me/submissions/69b252af-92b1-4f3d-9596-448650745358

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/DependentMoments.lean:L168-L185
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.avg_fibers. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments

-- ---- from OAI.Analysis.Littlewood.FiniteRank ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uK uV uι uW uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Linear
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

end Linear

section Counting
variable {V : Type uV} {W : Type uW} [AddGroup V] [AddGroup W] [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

omit [Fintype W] [DecidableEq V] in
lemma fiber_card_eq (f : V →+ W) (hf : Function.Surjective f) (x y : W) :
    (fiber f x).card=(fiber f y).card :=
  AddMonoidHom.card_fiber_eq_of_mem_range f (hf x) (hf y)

omit [DecidableEq V] in
lemma fiber_card_mul (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    Fintype.card W*(fiber f w).card=Fintype.card V := by
  have hc : Fintype.card V=∑ y : W, (fiber f y).card := by
    simpa only [Finset.card_univ,fiber] using
      (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset V))
        (t := (Finset.univ : Finset W)) (f := f) (by simp))
  simp_rw [fiber_card_eq f hf _ w] at hc
  simpa using hc.symm

end Counting

section PairCounting
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

end PairCounting
section PrimeRanks

end PrimeRanks

end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.DependentMoments ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uκ uA uJ uY uV uK uΩ uI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section ProductMoments
variable {κ : Type uκ} {A : Type uA} {J : Type uJ} {Y : Type uY} [Fintype κ] [DecidableEq κ] [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype J] [Fintype Y] [Nonempty Y]

end ProductMoments
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma avg_finset {V : Type uV} [Fintype V] (S : Finset V) (F : V → ℝ) :
    avg (fun v : S ↦ F v)=(∑ v∈S,F v)/(S.card : ℝ) := by
  simp only [avg,Fintype.card_coe,Finset.sum_coe_sort]

section ConditionalAverage
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma avg_fibers (f : V →ₗ[K] K) (hf : Function.Surjective f) (F : V → ℝ) :
    avg (fun s : K ↦ avg (fun v : fiber f s ↦ F v))=avg F := by
  classical
  have hcard (s : K) : (fiber f s).card=(fiber f 0).card :=
    fiber_card_eq f.toAddMonoidHom hf s 0
  simp_rw [avg_finset (fiber f _) F, hcard]
  dsimp [avg]
  rw [← Finset.sum_div,div_div]
  have he : ((fiber f 0).card : ℝ)*Fintype.card K=Fintype.card V := by
    have h : Fintype.card K*(fiber f (0 : K)).card=Fintype.card V :=
      fiber_card_mul f.toAddMonoidHom hf 0
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)
  rw [he]
  congr 1
  simp only [fiber,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

end ConditionalAverage
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section GoodRows
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Packing.rowsGoodDecidable
end GoodRows
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section AveragedVariance
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} {A : Type uA} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Nonempty A] [DecidableEq A]

end AveragedVariance
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uV,uK} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.avg_fibers.{uV,uK} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.avg_fibers.{uV,uK}
