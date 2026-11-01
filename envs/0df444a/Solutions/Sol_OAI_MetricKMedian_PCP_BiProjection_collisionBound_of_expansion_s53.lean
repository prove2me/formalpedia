-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:15:47.536726+00:00
-- url     : https://prove2.me/submissions/4c0c70cf-0073-4c7e-8785-e83b937ccbaf

import Mathlib
import Definitions.Def_OAIQ053K011
import Definitions.Def_OAIQ053K024
import Theorems.Thm_OAI_MetricKMedian_PCP_BiProjection_collision_sound_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_BiProjection_variance_bound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSpectralWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section FiniteEnergy
variable {S T : Type} [Fintype S] [Fintype T]

theorem pairing_sq_le (f g : S → ℝ) : pairing f g ^ 2 ≤ energy f * energy g :=
  expect_mul_sq_le_sq_mul_sq _ _ _

end FiniteEnergy

end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_L2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPL2

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section
variable {S : Type} [Fintype S]

lemma mean_sq_le_energy [Nonempty S] (f : S → ℝ) : (𝔼 x, f x)^2 ≤ energy f := by
  have h := pairing_sq_le (fun _ : S => (1:ℝ)) f
  simpa [pairing,energy] using h

end

end MetricKMedian.PCP

end Inline_PCPL2

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Norm
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionNorm

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {V T : Type} [Fintype V] [Fintype T]

lemma sq_nonneg (f : V → T → ℝ) : 0 ≤ sq f :=
  expect_nonneg (fun _ _ => sum_nonneg (fun _ _ => _root_.sq_nonneg _))
lemma norm_nonneg (f : V → T → ℝ) : 0 ≤ norm f := Real.sqrt_nonneg _
lemma norm_sq (f : V → T → ℝ) : norm f ^ 2=sq f := Real.sq_sqrt (sq_nonneg f)

variable [Nonempty V]

lemma inner_sq_le (f g : V → T → ℝ) : inner f g ^ 2 ≤ sq f*sq g := by
  let ff : V × T → ℝ := fun p => f p.1 p.2
  let gg : V × T → ℝ := fun p => g p.1 p.2
  have h := sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (V × T))) ff gg
  simp only [Fintype.sum_prod_type] at h
  unfold inner sq
  rw [Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card]
  have hn : 0 < (Fintype.card V:ℝ) := by positivity
  rw [div_pow,div_mul_div_comm]
  simpa only [ff,gg,pow_two] using (div_le_div_iff_of_pos_right (sq_pos_of_pos hn)).mpr h

lemma inner_le_norm (f g : V → T → ℝ) : inner f g ≤ norm f*norm g := by
  have h := inner_sq_le f g
  rw [← norm_sq f,← norm_sq g,← mul_pow] at h
  have hnn := mul_nonneg (norm_nonneg f) (norm_nonneg g)
  nlinarith

omit [Nonempty V] in
lemma sq_add (f g : V → T → ℝ) :
    sq (fun v t => f v t+g v t)=sq f+sq g+2*inner f g := by
  have he (v : V) (t : T) : (f v t+g v t)^2 =
      f v t^2+g v t^2+2*(f v t*g v t) := by ring
  unfold sq inner
  simp_rw [he,sum_add_distrib,← mul_sum,expect_add_distrib,← mul_expect]

lemma norm_add (f g : V → T → ℝ) :
    norm (fun v t => f v t+g v t) ≤ norm f+norm g := by
  have h := inner_le_norm f g
  have he := norm_sq (fun v t => f v t+g v t)
  rw [sq_add,← norm_sq f,← norm_sq g] at he
  nlinarith [norm_nonneg f,norm_nonneg g,norm_nonneg (fun v t => f v t+g v t)]

omit [Nonempty V] in
lemma norm_le_of_sq {f : V → T → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : sq f≤b^2) :
    norm f≤b := by
  rw [← norm_sq] at h
  nlinarith [norm_nonneg f]

lemma difference_bound (f g : V → T → ℝ) : norm f ≤ norm g+norm (fun v t => f v t-g v t) := by
  have h := norm_add g (fun v t => f v t-g v t)
  simpa only [add_sub_cancel] using h

end MixedNorm
end MetricKMedian.PCP

end Inline_PCPProjectionNorm

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Operator
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace ProjectionMass
variable {A B : Type} [Fintype A] [Fintype B]

lemma push_total (π : A → B) (f : A → ℝ) : ∑ b, push π f b=∑ a, f a := by
  unfold push
  rw [sum_comm]
  simp

omit [Fintype B] in
lemma push_nonneg (π : A → B) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (b : B) :
    0 ≤ push π f b := sum_nonneg (fun a _ => by split_ifs; exact hf a; exact le_rfl)

omit [Fintype B] in
lemma push_sub (π : A → B) (f g : A → ℝ) (b : B) :
    push π (fun a => f a-g a) b=push π f b-push π g b := by
  unfold push
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp

omit [Fintype B] in
lemma push_abs (π : A → B) (f : A → ℝ) (b : B) :
    |push π f b| ≤ push π (fun a => |f a|) b := by
  unfold push
  calc
    _ ≤ ∑ a, |if π a=b then f a else 0| := abs_sum_le_sum_abs _ _
    _ = _ := by apply sum_congr rfl; intro a _; split_ifs <;> simp

lemma push_sq_sum (π : A → B) (f : A → ℝ) :
    ∑ b, push π f b^2 ≤ (∑ a, |f a|)^2 := by
  calc
    _ ≤ ∑ b, push π (fun a => |f a|) b^2 := by
      apply sum_le_sum
      intro b _
      have h := push_abs π f b
      have hn := push_nonneg π (fun a => |f a|) (fun _ => abs_nonneg _) b
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (push π f b)) hn).mpr h
    _ ≤ (∑ b, push π (fun a => |f a|) b)^2 :=
      sum_sq_le_sq_sum_of_nonneg (fun b _ => push_nonneg π _ (fun _ => abs_nonneg _) b)
    _ = _ := by rw [push_total]
end ProjectionMass

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable (G : BiProjection U V D S A B)

omit [Fintype A] [Fintype B] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma source_expect (f : U × D → ℝ) :
    (𝔼 v, 𝔼 s, f (G.source v s))=𝔼 u, 𝔼 d, f (u,d) := by
  rw [← expect_prod (fun p : V × S => f (G.source p.1 p.2)),← expect_prod f]
  exact Fintype.expect_equiv G.edge.symm _ _ (fun _ => rfl)

omit [Fintype U] [Fintype V] [Fintype D] [Fintype T] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_sub (f g : U → A → T → ℝ) :
    G.push (fun u a t => f u a t-g u a t)=fun v b t => G.push f v b t-G.push g v b t := by
  funext v b t
  simp only [push,ProjectionMass.push_sub,expect_sub_distrib]

omit [Nonempty U] [Nonempty V] in
lemma collision_le_abs_total (f : U → A → T → ℝ) :
    G.collision f ≤ MixedNorm.sq (fun u t => ∑ a, |f u a t|) := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ 𝔼 v, ∑ b, ∑ t, 𝔼 s,
        (ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b)^2 := by
      apply expect_le_expect
      intro v _
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro t _
      exact mean_sq_le_energy _
    _ = 𝔼 v, 𝔼 s, ∑ t, ∑ b,
        (ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b)^2 := by
      simp_rw [← expect_sum_comm]
      apply expect_congr rfl
      intro v _
      apply expect_congr rfl
      intro s _
      exact sum_comm
    _ ≤ 𝔼 v, 𝔼 s, ∑ t, (∑ a, |f (G.source v s).1 a t|)^2 := by
      apply expect_le_expect
      intro v _
      apply expect_le_expect
      intro s _
      exact sum_le_sum (fun t _ => ProjectionMass.push_sq_sum _ _)
    _ = _ := by
      rw [G.source_expect (fun p : U × D => ∑ t, (∑ a, |f p.1 a t|)^2)]
      simp only [Fintype.expect_const]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionOperator

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {U T : Type} [Fintype U] [Nonempty U] [Fintype T]
omit [Nonempty U] in
lemma sq_coordinates (f : U → T → ℝ) : sq f=∑ t, energy (fun u => f u t) := by
  unfold sq energy
  exact expect_sum_comm _ _ _

lemma sq_mean_le (f : U → T → ℝ) : ∑ t, (𝔼 u, f u t)^2 ≤ sq f := by
  rw [sq_coordinates]
  exact sum_le_sum (fun t _ => mean_sq_le_energy _)

lemma sq_le_uniform (f : U → T → ℝ) (M : ℝ) (h : ∀ u, ∑ t, f u t^2≤M) : sq f≤M := by
  unfold sq
  exact (expect_le_expect (fun u _ => h u)).trans_eq (Fintype.expect_const M)
end MixedNorm

end MetricKMedian.PCP

end Inline_PCPProjectionExpansion

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_MassNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPMassNormalize

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MassNormalize
variable {A : Type} [Fintype A] [Inhabited A]

lemma nonneg (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (H : ℝ) (hH : 0 ≤ H) (a : A) :
    0 ≤ normalized f H a := by
  unfold normalized
  split_ifs
  · exact hH
  · exact le_rfl
  · exact mul_nonneg (div_nonneg hH (sum_nonneg (fun a _ => hf a))) (hf a)

lemma total (f : A → ℝ) (H : ℝ) : ∑ a, normalized f H a=H := by
  unfold normalized
  by_cases hz : (∑ a, f a)=0
  · simp only [hz,ite_true]
    simp
  · simp only [hz,ite_false,← mul_sum]
    exact div_mul_cancel₀ H hz

omit [Inhabited A] in
lemma zero_entries (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (hz : (∑ a, f a)=0) (a : A) : f a=0 := by
  exact (sum_eq_zero_iff_of_nonneg (fun a _ => hf a)).mp hz a (mem_univ _)

lemma l1_error (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (H : ℝ) (hH : 0 ≤ H) :
    (∑ a, |f a-normalized f H a|)=|(∑ a, f a)-H| := by
  by_cases hz : (∑ a, f a)=0
  · have he : f=fun _ => 0 := funext (zero_entries f hf hz)
    rw [he]
    unfold normalized
    simp only [sum_const_zero,ite_true,zero_sub,abs_neg]
    simp only [apply_ite abs,abs_of_nonneg hH,abs_zero]
    simp
  · have hp : 0 ≤ ∑ a, f a := sum_nonneg (fun a _ => hf a)
    unfold normalized
    simp only [hz,ite_false]
    calc
      _ = ∑ a, |1-H/(∑ a, f a)| *f a := by
        apply sum_congr rfl
        intro a _
        rw [show f a-(H/(∑ a, f a))*f a=(1-H/(∑ a, f a))*f a by ring,
          abs_mul,abs_of_nonneg (hf a)]
      _ = |1-H/(∑ a, f a)| *(∑ a, f a) := (mul_sum _ _ _).symm
      _ = |(1-H/(∑ a, f a))*(∑ a, f a)| := by rw [abs_mul,abs_of_nonneg hp]
      _ = _ := by congr 1; field_simp
end MassNormalize
end MetricKMedian.PCP

end Inline_PCPMassNormalize

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Contraction
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BiProjection.prod_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionContraction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_sq (f : U → A → T → ℝ) : G.collisionNorm f^2=G.collision f :=
  MixedNorm.norm_sq _
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_nonneg (f : U → A → T → ℝ) : 0 ≤ G.collisionNorm f :=
  MixedNorm.norm_nonneg _
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_difference (f g : U → A → T → ℝ) :
    G.collisionNorm f ≤ G.collisionNorm g+G.collisionNorm (fun u a t => f u a t-g u a t) := by
  unfold collisionNorm
  rw [G.push_sub]
  exact MixedNorm.difference_bound _ _
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_le (f : U → A → T → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : G.collision f≤b^2) : G.collisionNorm f≤b := MixedNorm.norm_le_of_sq hb h

theorem collision_contraction (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : G.Sound s) (hG : G.Expands γ)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ u, ∑ t, (∑ a, f u a t)^2≤M^2) :
    G.collision f ≤ (1-γ*((1-s)/4)^2)*M^2 := by
  let : Inhabited A := ⟨Classical.choice inferInstance⟩
  let H : T → ℝ := fun t => 𝔼 u, ∑ a, f u a t
  let g : U → A → T → ℝ := fun u a t => MassNormalize.normalized (fun a => f u a t) (H t) a
  let W : ℝ := MixedNorm.sq (fun u t => (∑ a, f u a t)-H t)
  have hH (t : T) : 0 ≤ H t := expect_nonneg (fun u _ => sum_nonneg (fun a _ => hf u a t))
  have hg (u : U) (a : A) (t : T) : 0 ≤ g u a t := MassNormalize.nonneg _ (fun a => hf u a t) _ (hH t) a
  have hgt (u : U) (t : T) : ∑ a, g u a t=H t := MassNormalize.total _ _
  have hmean : ∑ t, H t^2≤M^2 := (MixedNorm.sq_mean_le (fun u t => ∑ a, f u a t)).trans
    (MixedNorm.sq_le_uniform _ _ hm)
  have hcg : G.collision g≤ s *M^2 := (G.collision_sound_s53 s hs g hg H hH hgt).trans
    (mul_le_mul_of_nonneg_left hmean hs0)
  have herr : G.collision (fun u a t => f u a t-g u a t)≤W := by
    have hh := G.collision_le_abs_total (fun u a t => f u a t-g u a t)
    have he (u : U) (t : T) : (∑ a, |f u a t-g u a t|)=|(∑ a, f u a t)-H t| :=
      MassNormalize.l1_error _ (fun a => hf u a t) _ (hH t)
    simp only [MixedNorm.sq,he,sq_abs] at hh
    exact hh
  have hvar : γ*W≤M^2-G.collision f := G.variance_bound_s53 γ hG f hf M hm
  let θ : ℝ := (1-s)/4
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1/4 := by dsimp [θ]; linarith
  by_cases hw : W ≤ θ^2*M^2
  · have hnerr : G.collisionNorm (fun u a t => f u a t-g u a t)≤θ*M := by
      apply G.collisionNorm_le _ _ (mul_nonneg hθ hM)
      simpa only [mul_pow] using herr.trans hw
    have hng : G.collisionNorm g≤((1+s)/2)*M := by
      apply G.collisionNorm_le _ _ (mul_nonneg (by positivity) hM)
      apply hcg.trans
      have hp : s≤((1+s)/2)^2 := by nlinarith [sq_nonneg (1-s)]
      simpa only [mul_pow] using mul_le_mul_of_nonneg_right hp (sq_nonneg M)
    have hn : G.collisionNorm f≤(1-θ)*M := by
      have hh := G.collisionNorm_difference f g
      dsimp [θ] at *
      linarith
    have hq : G.collision f≤((1-θ)*M)^2 := by
      rw [← G.collisionNorm_sq]
      exact pow_le_pow_left₀ (G.collisionNorm_nonneg f) hn 2
    have hc : (1-θ)^2≤1-γ*θ^2 := by
      have hh : γ*θ^2≤θ^2 := mul_le_of_le_one_left (sq_nonneg θ) hγ1
      nlinarith [mul_nonneg hθ (show 0 ≤ 1-θ by linarith)]
    have hfinal : ((1-θ)*M)^2 ≤ (1-γ*θ^2)*M^2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg M)
    exact hq.trans hfinal
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hw) hγ0
    dsimp [θ] at hh
    nlinarith only [hvar,hh]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionContraction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

lemma collisionBound_of_expansion_s53_oai (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : G.Sound s) (hG : G.Expands γ) :
    G.CollisionBound (1-γ*((1-s)/4)^2) := by
  intro T _ f hf M hM hm
  have hh := G.collision_contraction s γ hs0 hs1 hγ0 hγ1 hs hG f hf
    (Real.sqrt M) (Real.sqrt_nonneg M) (by simpa only [Real.sq_sqrt hM] using hm)
  simpa only [Real.sq_sqrt hM] using hh

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionBound

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53_oai := @OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53_oai
