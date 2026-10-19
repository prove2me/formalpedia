-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.exists_few_bad_centers_averaged
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:23:48.832607+00:00
-- url     : https://prove2.me/submissions/0db866fb-3a53-4cd1-9bcf-498283b01bd3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/DependentMoments.lean:L484-L502
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.exists_few_bad_centers_averaged. The node keeps its source
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

-- ---- from OAI.Analysis.Littlewood.Averages ----
namespace OAI

universe uΩ uI uΛ uK uA uJ uY

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Average
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

omit [Nonempty Ω] in
lemma avg_mul_const (f : Ω → ℝ) (c : ℝ) : avg (fun ω ↦ f ω*c)=avg f*c := by
  simp [avg,← Finset.sum_mul]; ring
omit [Nonempty Ω] in
lemma avg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω≤g ω) : avg f≤avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)
omit [Nonempty Ω] in
lemma avg_sum {I : Type uI} (S : Finset I) (f : I → Ω → ℝ) :
    avg (fun ω ↦ ∑ i ∈ S, f i ω)=∑ i ∈ S, avg (f i) := by
  dsimp [avg]
  rw [Finset.sum_comm,Finset.sum_div]
lemma exists_le_avg (f : Ω → ℝ) : ∃ ω, f ω≤avg f := by
  have he : (∑ ω, f ω) = ∑ _ω : Ω, avg f := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,avg]
    field_simp
  obtain ⟨ω,_,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := Ω)) he.le
  exact ⟨ω,h⟩

omit [Nonempty Ω] in
lemma avg_comm {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω → Λ → ℝ) :
    avg (fun ω ↦ avg (f ω))=avg (fun x ↦ avg (fun ω ↦ f ω x)) := by
  dsimp [avg]
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

omit [Nonempty Ω] in
lemma avg_chebyshev {Z : Ω → ℝ} (p : ℝ) {t : ℝ} (ht : 0<t) :
    avg (fun ω ↦ if t≤|Z ω-p| then 1 else 0) ≤
      avg (fun ω ↦ (Z ω-p)^2)/t^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos ht),← avg_mul_const]
  apply avg_mono
  intro ω
  split_ifs with h
  · nlinarith [sq_abs (Z ω-p)]
  · simp only [zero_mul]; positivity

end Average
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

section ConditionalAverage
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

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

lemma exists_few_bad_centers_total {Ω : Type uΩ} {I : Type uI} [Fintype Ω] [Nonempty Ω]
    [Fintype I] (Z : I → Ω → ℝ) (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : (∑ i, avg (fun ω ↦ (Z i ω-p)^2))≤a) :
    ∃ ω, ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ) ≤ a/t^2 := by
  classical
  let W : Ω → ℝ := fun ω ↦ ∑ i : I, if t≤|Z i ω-p| then 1 else 0
  obtain ⟨ω,hω⟩ := exists_le_avg W
  refine ⟨ω,?_⟩
  have he : ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ)=W ω := by
    simp [W,Finset.sum_boole]
  rw [he]
  apply hω.trans
  dsimp [W]
  rw [avg_sum]
  calc
    _ ≤ ∑ i, avg (fun ω ↦ (Z i ω-p)^2)/t^2 :=
      Finset.sum_le_sum (fun i _ ↦ avg_chebyshev p ht)
    _ = (∑ i, avg (fun ω ↦ (Z i ω-p)^2))/t^2 := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hZ (sq_nonneg _)

lemma exists_few_bad_centers_averaged {Ω : Type uΩ} {I : Type uI} {K : Type uK} [Fintype Ω] [Nonempty Ω]
    [Fintype I] [Fintype K] [Nonempty K] (Z : I → K → Ω → ℝ)
    (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : ∀ i, avg (fun ω ↦ avg (fun s ↦ (Z i s ω-p)^2))≤a) :
    ∃ ω, ((Finset.univ.filter (fun v : I × K ↦ t≤|Z v.1 v.2 ω-p|)).card : ℝ) ≤
      Fintype.card I*Fintype.card K*a/t^2 := by
  classical
  apply exists_few_bad_centers_total (Ω := Ω) (I := I × K)
    (fun (v : I × K) (ω : Ω) ↦ Z v.1 v.2 ω) p (a := Fintype.card I*Fintype.card K*a) ht
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _i : I, (Fintype.card K : ℝ)*a := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hZ i
      rw [avg_comm,avg] at hi
      have hcard : (0 : ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
      simpa only [mul_comm a] using ((div_le_iff₀ hcard).mp hi)
    _ = _ := by simp; ring

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uK,uΩ,uI} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.exists_few_bad_centers_averaged.{uK,uΩ,uI} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.exists_few_bad_centers_averaged.{uK,uΩ,uI}
