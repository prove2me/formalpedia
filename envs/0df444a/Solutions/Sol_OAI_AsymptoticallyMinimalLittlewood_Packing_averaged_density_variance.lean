-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.averaged_density_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:22:10.670006+00:00
-- url     : https://prove2.me/submissions/c913b4fa-ca1a-4cb8-9754-8f7d389bf7a7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/DependentMoments.lean:L404-L453
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.averaged_density_variance. The node keeps its source
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
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_avg_fibers
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_conditional_card_event
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_selections_variance

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

lemma avg_const (c : ℝ) : avg (fun _ : Ω ↦ c) = c := by
  simp [avg, Fintype.card_ne_zero]
omit [Nonempty Ω] in
lemma avg_add (f g : Ω → ℝ) : avg (fun ω ↦ f ω+g ω)=avg f+avg g := by
  simp [avg,Finset.sum_add_distrib,add_div]
omit [Nonempty Ω] in
lemma avg_mul_const (f : Ω → ℝ) (c : ℝ) : avg (fun ω ↦ f ω*c)=avg f*c := by
  simp [avg,← Finset.sum_mul]; ring
omit [Nonempty Ω] in
lemma avg_const_mul (c : ℝ) (f : Ω → ℝ) : avg (fun ω ↦ c*f ω)=c*avg f := by
  simpa only [mul_comm c] using avg_mul_const f c
omit [Nonempty Ω] in
lemma avg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω≤g ω) : avg f≤avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)
omit [Nonempty Ω] in
lemma avg_sum {I : Type uI} (S : Finset I) (f : I → Ω → ℝ) :
    avg (fun ω ↦ ∑ i ∈ S, f i ω)=∑ i ∈ S, avg (f i) := by
  dsimp [avg]
  rw [Finset.sum_comm,Finset.sum_div]
omit [Nonempty Ω] in
lemma avg_comm {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω → Λ → ℝ) :
    avg (fun ω ↦ avg (f ω))=avg (fun x ↦ avg (fun ω ↦ f ω x)) := by
  dsimp [avg]
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

omit [Nonempty Ω] in
lemma avg_prod_type {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω × Λ → ℝ) :
    avg f = avg (fun ω ↦ avg (fun x ↦ f (ω,x))) := by
  simp only [avg,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,← Finset.sum_div]
  ring

omit [Nonempty Ω] in
lemma avg_bad_union {I : Type uI} (S : Finset I) (P : I → Ω → Prop)
    [∀ i, DecidablePred (P i)] :
    avg (fun ω ↦ if ∃ i∈S, P i ω then 1 else 0) ≤
      ∑ i∈S, avg (fun ω ↦ if P i ω then 1 else 0) := by
  classical
  rw [← avg_sum]
  apply avg_mono
  intro ω
  split_ifs with h
  · obtain ⟨i,hi,hP⟩ := h
    exact (show (1 : ℝ) ≤ (if P i ω then 1 else 0) by simp [hP]).trans
      (Finset.single_le_sum (f := fun j ↦ if P j ω then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) hi)
  · exact Finset.sum_nonneg (fun j _ ↦ by split_ifs <;> norm_num)

end Average
end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI

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

omit [Fintype W] [DecidableEq V] in
lemma fiber_nonempty (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    (fiber f w).Nonempty := by
  obtain ⟨v,hv⟩ := hf w
  exact ⟨v,by simp [hv]⟩

end Counting

section PairCounting
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [Fintype K] [DecidableEq V] in
lemma joint_fiber_eq (f g : V →ₗ[K] K) (s t : K) :
    (fiber f s).filter (fun v ↦ g v=t) = fiber (f.prod g) (s,t) := by
  ext v
  simp [fiber,Prod.ext_iff]

omit [Fintype K] [DecidableEq V] in
lemma conditional_fiber_card (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s t u : K) :
    ((fiber f s).filter (fun v ↦ g v=t)).card =
    ((fiber f s).filter (fun v ↦ g v=u)).card := by
  simp only [joint_fiber_eq]
  exact fiber_card_eq (f.prod g).toAddMonoidHom hfg _ _

omit [DecidableEq V] in
lemma conditional_fiber_count (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s t : K) :
    Fintype.card K*((fiber f s).filter (fun v ↦ g v=t)).card=(fiber f s).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := fiber f s)
    (t := (Finset.univ : Finset K)) (f := g) (by simp)
  simp_rw [conditional_fiber_card f g hfg s _ t] at h
  simpa using h.symm

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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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
lemma avg_fiber_event (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s : K) (S : Finset K) :
    avg (fun v : fiber f s ↦ if g v∈S then (1 : ℝ) else 0)=
      (S.card : ℝ)/Fintype.card K := by
  classical
  rw [avg_finset (fiber f s) (fun v ↦ if g v∈S then (1 : ℝ) else 0)]
  simp only [Finset.sum_boole]
  have hc := conditional_card_event f g hfg s S
  rw [hc,Nat.cast_mul]
  have hn := conditional_fiber_count f g hfg s 0
  have hF : 0<(fiber f s).card := by
    apply Finset.card_pos.mpr
    obtain ⟨y,hy⟩ := hfg (s,0)
    refine ⟨y,?_⟩
    exact mem_fiber.mpr (congrArg Prod.fst hy)
  have hK : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hF' : ((fiber f s).card : ℝ)≠0 := by positivity
  have hn' : (Fintype.card K : ℝ)*((fiber f s).filter (fun v ↦ g v=0)).card=
      (fiber f s).card := by exact_mod_cast hn
  field_simp
  nlinarith only [hn']

omit [DecidableEq V] in
lemma avg_uniform_event (f : V →ₗ[K] K) (hf : Function.Surjective f) (S : Finset K) :
    avg (fun v : V ↦ if f v∈S then (1 : ℝ) else 0)=
      (S.card : ℝ)/Fintype.card K := by
  rw [← avg_fibers f hf]
  have hh (s : K) : avg (fun v : fiber f s ↦ if f v∈S then (1 : ℝ) else 0)=
      if s∈S then 1 else 0 := by
    have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
    simp_rw [mem_fiber.mp (Subtype.property _)]
    exact avg_const _
  simp_rw [hh]
  simp [avg]

omit [DecidableEq V] in
lemma avg_cross_chunks {κ : Type uκ} [DecidableEq κ]
    (f g h : V →ₗ[K] K) (hfg : Function.Surjective (f.prod g))
    (chunk : K → κ) (s : K) {B : ℝ}
    (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun yy : fiber f s × fiber f s ↦
      if chunk (g yy.1)=chunk (h yy.2) then (1 : ℝ) else 0) ≤
      B/Fintype.card K := by
  have : Nonempty (fiber f s) := by
    obtain ⟨y,hy⟩ := hfg (s,0)
    exact ⟨⟨y,mem_fiber.mpr (congrArg Prod.fst hy)⟩⟩
  rw [avg_prod_type,avg_comm]
  apply (avg_mono (fun y ↦ ?_)).trans_eq (avg_const _)
  have he := avg_fiber_event f g hfg s (Finset.univ.filter (fun t ↦ chunk t=chunk (h y)))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at he
  rw [he]
  exact div_le_div_of_nonneg_right (hB _) (Nat.cast_nonneg _)

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
omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] in
lemma sum_form_surjective (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) : Function.Surjective (f+g) := by
  classical
  intro s
  obtain ⟨v,hv⟩ := hfg (s,0)
  exact ⟨v,by simp [show f v=s from congrArg Prod.fst hv,
    show g v=0 from congrArg Prod.snd hv]⟩

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] in
lemma sub_form_surjective (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) : Function.Surjective (f-g) := by
  classical
  intro s
  obtain ⟨v,hv⟩ := hfg (s,0)
  exact ⟨v,by simp [show f v=s from congrArg Prod.fst hv,
    show g v=0 from congrArg Prod.snd hv]⟩

omit [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] [Fintype J] in
lemma rowsGood_injective (g : J → V →ₗ[K] K) (G S : Finset K) (chunk : K → κ)
    (hchunk : ∀ t∈G, ∀ u∈G, chunk t=chunk u → t+u∈S ∨ t-u∈S)
    {y : V} (hy : rowsGood g G S y) : Function.Injective (fun j ↦ chunk (g j y)) := by
  classical
  intro j l hjl
  by_contra hne
  rcases hchunk _ (hy.1 j) _ (hy.1 l) hjl with h | h
  · exact (hy.2 j l hne).1 h
  · exact (hy.2 j l hne).2 h

omit [Fintype K] [Fintype V] [DecidableEq V] in
lemma rows_bad_indicator (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) :
    (if rowsGood g G S y then (0 : ℝ) else 1) ≤
      (∑ j, if g j y∉G then (1 : ℝ) else 0)+
      ∑ jl : J × J, if jl.1≠jl.2 then
        (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
        (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0 := by
  classical
  have hnon (P : Prop) : 0≤(if P then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hn₁ : 0≤∑ j, if g j y∉G then (1 : ℝ) else 0 := Finset.sum_nonneg (fun j _ ↦ by split_ifs <;> norm_num)
  have hn₂ : 0≤∑ jl : J × J, if jl.1≠jl.2 then
      (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
      (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0 := by
    apply Finset.sum_nonneg
    intro jl _
    split_ifs <;> norm_num
  split_ifs with h
  · linarith
  · by_cases hloc : ∀ j, g j y∈G
    · obtain ⟨j,l,hjl,hbad⟩ : ∃ j l, j≠l ∧ ¬(g j y+g l y∉S ∧ g j y-g l y∉S) := by
        have hh : ¬ ∀ j l, j≠l → g j y+g l y∉S ∧ g j y-g l y∉S :=
          fun hh ↦ h ⟨hloc,hh⟩
        obtain ⟨j,hj⟩ := not_forall.mp hh
        obtain ⟨l,hl⟩ := not_forall.mp hj
        obtain ⟨hne,hbad⟩ := Classical.not_imp.mp hl
        exact ⟨j,l,hne,hbad⟩
      have hp : (1 : ℝ)≤(if g j y+g l y∈S then 1 else 0)+
          (if g j y-g l y∈S then 1 else 0) := by
        split_ifs <;> simp_all
      have hs := Finset.single_le_sum (f := fun jl : J × J ↦ if jl.1≠jl.2 then
        (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
        (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0)
        (fun jl _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ (j,l))
      simp only [ite_eq_left hjl] at hs
      linarith
    · obtain ⟨j,hj⟩ := not_forall.mp hloc
      have hs := Finset.single_le_sum (f := fun j ↦ if g j y∉G then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ j)
      simp only [hj,not_false_eq_true,ite_true] at hs
      linarith

omit [DecidableEq V] in
lemma avg_bad_rows (g : J → V →ₗ[K] K)
    (hg : ∀ j, Function.Surjective (g j))
    (hpair : ∀ j l, j≠l → Function.Surjective ((g j).prod (g l)))
    (G S : Finset K) :
    avg (fun y ↦ if rowsGood g G S y then (0 : ℝ) else 1) ≤
      (Fintype.card J : ℝ)*(Fintype.card K-G.card)/Fintype.card K+
        2*(Fintype.card J : ℝ)^2*S.card/Fintype.card K := by
  classical
  have : Nonempty V := ⟨0⟩
  apply (avg_mono (rows_bad_indicator g G S)).trans
  rw [avg_add,avg_sum,avg_sum]
  have hloc (j : J) : avg (fun y ↦ if g j y∉G then (1 : ℝ) else 0)=
      (Fintype.card K-G.card : ℝ)/Fintype.card K := by
    have he := avg_uniform_event (g j) (hg j) (Finset.univ \ G)
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.card_sdiff,
      Finset.inter_univ,Finset.card_univ] at he
    rw [Nat.cast_sub (Finset.card_le_univ G)] at he
    exact he
  have hpair' (jl : J × J) : avg (fun y ↦ if jl.1≠jl.2 then
      (if g jl.1 y+g jl.2 y∈S then (1 : ℝ) else 0)+
      (if g jl.1 y-g jl.2 y∈S then 1 else 0) else 0) ≤
        2*(S.card : ℝ)/Fintype.card K := by
    by_cases hjl : jl.1≠jl.2
    · simp only [ite_eq_left hjl,avg_add]
      have hs := avg_uniform_event (g jl.1+g jl.2) (sum_form_surjective _ _ (hpair _ _ hjl)) S
      have hd := avg_uniform_event (g jl.1-g jl.2) (sub_form_surjective _ _ (hpair _ _ hjl)) S
      simp only [LinearMap.add_apply,LinearMap.sub_apply] at hs hd
      rw [hs,hd]
      ring_nf
      exact le_refl _
    · simp only [ite_eq_right hjl,avg_const]
      positivity
  simp_rw [hloc]
  apply add_le_add_right (Finset.sum_le_sum (fun jl _ ↦ hpair' jl)) _ |>.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

omit [DecidableEq J] [DecidableEq V] in
lemma avg_cross_rows [DecidableEq κ] (f : V →ₗ[K] K) (g : J → V →ₗ[K] K)
    (hfg : ∀ j, Function.Surjective (f.prod (g j)))
    (hf : Function.Surjective f) (chunk : K → κ) (s : K) {B : ℝ}
    (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun yy : fiber f s × fiber f s ↦
      if ∃ j l, chunk (g j yy.1)=chunk (g l yy.2) then (1 : ℝ) else 0) ≤
        (Fintype.card J : ℝ)^2*B/Fintype.card K := by
  classical
  have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
  calc
    _ = avg (fun yy : fiber f s × fiber f s ↦
        if ∃ jl∈(Finset.univ : Finset (J × J)), chunk (g jl.1 yy.1)=chunk (g jl.2 yy.2)
        then (1 : ℝ) else 0) := by simp
    _ ≤ ∑ jl : J × J, avg (fun yy : fiber f s × fiber f s ↦
        if chunk (g jl.1 yy.1)=chunk (g jl.2 yy.2) then (1 : ℝ) else 0) := avg_bad_union _ _
    _ ≤ ∑ _jl : J × J, B/Fintype.card K := Finset.sum_le_sum (fun jl _ ↦
      avg_cross_chunks f (g jl.1) (g jl.2) (hfg jl.1) chunk s hB)
    _ = _ := by simp [Fintype.card_prod,pow_two]; ring

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

omit [DecidableEq V] in
/-- Averaging over the anchored coordinate removes even the exceptional
centers. This quantitative statement is used before pruning the slot graph. -/
lemma averaged_density_variance (f : V →ₗ[K] K) (g : J → V →ₗ[K] K)
    (hf : Function.Surjective f)
    (hg : ∀ j, Function.Surjective (g j))
    (hfg : ∀ j, Function.Surjective (f.prod (g j)))
    (hpair : ∀ j l, j≠l → Function.Surjective ((g j).prod (g l)))
    (G S : Finset K) (chunk : K → κ)
    (hchunk : ∀ t∈G, ∀ u∈G, chunk t=chunk u → t+u∈S ∨ t-u∈S)
    (hit : J → K → (κ → A) → Prop) [∀ j t ω, Decidable (hit j t ω)]
    (hhit : ∀ j t, t∈G → ∃ a : A, ∀ ω, hit j t ω ↔ ω (chunk t)=a)
    {B : ℝ} (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun ω : κ → A ↦ avg (fun s : K ↦
      (avg (fun y : fiber f s ↦ ∏ j, if hit j (g j y) ω then (1 : ℝ) else 0)-
        (1/(Fintype.card A : ℝ))^(Fintype.card J))^2)) ≤
      3*(2*((Fintype.card J : ℝ)*(Fintype.card K-G.card)/Fintype.card K+
          2*(Fintype.card J : ℝ)^2*S.card/Fintype.card K)+
        (Fintype.card J : ℝ)^2*B/Fintype.card K) := by
  classical
  have ha : ∀ j t, ∃ a : A, t∈G → ∀ ω, hit j t ω ↔ ω (chunk t)=a := by
    intro j t
    by_cases ht : t∈G
    · obtain ⟨a,ha⟩ := hhit j t ht
      exact ⟨a,fun _ ↦ ha⟩
    · exact ⟨Classical.arbitrary A,fun h ↦ (ht h).elim⟩
  choose a ha using ha
  have hs (s : K) :
      avg (fun ω : κ → A ↦
        (avg (fun y : fiber f s ↦ ∏ j, if hit j (g j y) ω then (1 : ℝ) else 0)-
          (1/(Fintype.card A : ℝ))^(Fintype.card J))^2) ≤
        3*(2*avg (fun y : fiber f s ↦ if rowsGood g G S y then (0 : ℝ) else 1)+
          (Fintype.card J : ℝ)^2*B/Fintype.card K) := by
    have : Nonempty (fiber f s) := (fiber_nonempty f.toAddMonoidHom hf s).coe_sort
    apply selections_variance
      (fun j (y : fiber f s) ω ↦ if hit j (g j y) ω then (1 : ℝ) else 0)
      (fun y j ↦ chunk (g j y)) (fun y j ↦ a j (g j y))
      (fun y ↦ rowsGood g G S y)
    · intro j y ω; split_ifs <;> norm_num
    · intro y hy; exact rowsGood_injective g G S chunk hchunk hy
    · intro y hy j ω
      simp only [ha j (g j y) (hy.1 j) ω]
    · exact le_refl _
    · exact avg_cross_rows f g hfg hf chunk s hB
  rw [avg_comm]
  apply (avg_mono hs).trans
  have he := avg_fibers f hf (fun y ↦ if rowsGood g G S y then (0 : ℝ) else 1)
  rw [avg_const_mul,avg_add,avg_const_mul,avg_const,he]
  have hb := avg_bad_rows g hg hpair G S
  linarith

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


theorem solution.{uκ,uA,uJ,uV,uK} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.averaged_density_variance.{uκ,uA,uJ,uV,uK} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.averaged_density_variance.{uκ,uA,uJ,uV,uK}
