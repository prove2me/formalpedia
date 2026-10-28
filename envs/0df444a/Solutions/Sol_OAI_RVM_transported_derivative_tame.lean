-- Prove2me | solution 1 for OAI.RVM.transported_derivative_tame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:45:42.004264+00:00
-- url     : https://prove2.me/submissions/865000a4-2e0d-4afc-ac79-39cbca0753b7

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_SmoothLorentzFlow_backward_derivative_tame
import Theorems.Thm_OAI_RVM_SmoothLorentzFlow_reversePath_derivatives_bound
import Theorems.Thm_OAI_RVM_exists_smoothLorentzFlow

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

namespace SmoothLorentzFlow

lemma transport_for {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,F.forward z t)=s.f (0,z) := by
  have hd (r : ℝ) : HasDerivAt (fun r => s.f (r,F.forward z r)) (0:ℝ) r := by
    have hh := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (F.ode z r))
    change HasDerivAt (fun r => s.f (r,F.forward z r))
      (fderiv ℝ s.f (r,F.forward z r) (1,lorentzField E B (r,F.forward z r))) r at hh
    rw [hV] at hh
    exact hh
  have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [F.initial] using he

lemma transport_for_inverse {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,z)=s.f (0,F.backward (t,z)) := by
  simpa only [F.right_inverse] using F.transport_for hf hV t (F.backward (t,z))

end SmoothLorentzFlow

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_TameDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma tame_iteratedFDeriv_comp (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : F → G) (f : E → F), ContDiff ℝ ∞ g  →  ContDiff ℝ ∞ f  →
      ∀ x, (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i g (f x)‖ ≤ A)  →
        (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i f x‖ ≤ A)  →
        ‖iteratedFDeriv ℝ (n+1) (g ∘ f) x‖ ≤
          C*(1+‖iteratedFDeriv ℝ (n+1) g (f x)‖+‖iteratedFDeriv ℝ (n+1) f x‖) := by
  let c : ℕ → ℝ := fun i => (n.choose i : ℝ)*i.factorial*A^(i+1)
  let S := ∑ i∈Finset.range (n+1), c i
  refine ⟨A+S*(A+1),by dsimp [S,c]; positivity,?_⟩
  intro g f hg hf x hgl hfl
  let Mg := ‖iteratedFDeriv ℝ (n+1) g (f x)‖
  let Mf := ‖iteratedFDeriv ℝ (n+1) f x‖
  have hMg : 0 ≤ Mg := norm_nonneg _
  have hMf : 0 ≤ Mf := norm_nonneg _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hcn (i : ℕ) : 0 ≤ c i := by dsimp [c]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hcn i)
  have hfg : fderiv ℝ (g ∘ f) =
      (fun y => ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f y)) (fderiv ℝ f y)) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by simp) (f y)) (hf.differentiable (by simp) y)
  have hcomp (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖ ≤ i.factorial*(A+Mg)*A^i := by
    apply norm_iteratedFDeriv_comp_le (n:=i) (hg.fderiv_right (m:=∞) (by simp)) hf (by exact_mod_cast le_top) x
    · intro j hj
      rw [norm_iteratedFDeriv_fderiv]
      by_cases hjn : j+1 ≤ n
      · exact (hgl (j+1) (by omega) hjn).trans (le_add_of_nonneg_right hMg)
      · have he : j+1=n+1 := by omega
        rw [he]
        exact le_add_of_nonneg_left hA0
    · intro j hj hj'
      exact (hfl j hj (hj'.trans hi)).trans (le_self_pow₀ hA (by omega))
  have hh := (ContinuousLinearMap.compL ℝ E F G).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    ((hg.fderiv_right (m:=∞) (by simp)).comp hf) (hf.fderiv_right (m:=∞) (by simp)) x (n:=n) (by exact_mod_cast le_top)
    (ContinuousLinearMap.norm_compL_le ℝ E F G)
  have hterm (i : ℕ) (hi : i∈Finset.range (n+1)) :
      (n.choose i : ℝ)*‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖*
        ‖iteratedFDeriv ℝ (n-i) (fderiv ℝ f) x‖  ≤
      c i*(A+Mg)+(if i=0 then A*Mf else 0) := by
    have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
    rw [norm_iteratedFDeriv_fderiv]
    by_cases hi0 : i=0
    · subst i
      simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,norm_iteratedFDeriv_zero,Function.comp_apply,
        Nat.sub_zero,ite_true]
      have hg1 : ‖fderiv ℝ g (f x)‖ ≤ A := by simpa only [norm_iteratedFDeriv_one] using hgl 1 le_rfl hn
      exact (mul_le_mul_of_nonneg_right hg1 hMf).trans (le_add_of_nonneg_left (mul_nonneg (hcn 0) (add_nonneg hA0 hMg)))
    · rw [ite_eq_right hi0,add_zero]
      have hlow := hfl (n-i+1) (by omega) (by omega)
      calc
        _  ≤  (n.choose i : ℝ)*(i.factorial*(A+Mg)*A^i)*A := by
          gcongr
          exact hcomp i hi'
        _ = c i*(A+Mg) := by dsimp [c]; rw [pow_succ]; ring
  rw [← norm_iteratedFDeriv_fderiv,hfg]
  refine hh.trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show 0<n+1 by omega,ite_true]
  change S*(A+Mg)+A*Mf ≤ (A+S*(A+1))*(1+Mg+Mf)
  nlinarith [mul_nonneg hS hMg,mul_nonneg hS hMf,mul_nonneg (mul_nonneg hS hA0) hMg,
    mul_nonneg (mul_nonneg hS hA0) hMf,mul_nonneg hA0 hMg]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleTame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma smooth_compact_jets_bound {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hb (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv (i:ℕ))
    exact ⟨max C 0,le_max_right _ _,fun x => (hC x).trans (le_max_left _ _)⟩
  choose C hC hbound using hb
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro i hi x
  exact (hbound ⟨i,by omega⟩ x).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ _))

lemma transported_derivative_tame_oai {d : Datum} (hd : Admissible d)
    (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ (s : Solution), PicardRegular d s → TransportFor s E B →
      ∀ T : ℝ, T∈Icc (0:ℝ) 1 → SpatialJetBound n T A E B →
      ∀ H : ℝ, 0 ≤ H →
      (∀ t∈Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun y => E (t,y)) x‖ ≤ H ∧
        ‖iteratedFDeriv ℝ (n+1) (fun y => B (t,y)) x‖ ≤ H) →
      ∀ t∈Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ (n+1) (fun w => s.f (t,w)) z‖ ≤ C*(1+H) := by
  obtain ⟨D,hD,hdjet⟩ := smooth_compact_jets_bound hd.1 hd.2.1 (n+1)
  obtain ⟨L,hL,hlow⟩ := SmoothLorentzFlow.reversePath_derivatives_bound n A hA
  obtain ⟨K,hK,htop⟩ := SmoothLorentzFlow.backward_derivative_tame n hn A hA
  obtain ⟨C,hC,hcomp⟩ := tame_iteratedFDeriv_comp (E:=Phase) (F:=Phase) (G:=ℝ) n hn (1+D+L) (by linarith)
  refine ⟨C*(1+D+K),by positivity,?_⟩
  intro E B hE hB s hs hV T hT hb H hH hh t ht z
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  have hback : ContDiff ℝ ∞ (fun z => F.backward (t,z)) :=
    F.smooth_backward.comp (contDiff_const.prodMk contDiff_id)
  have hrep : (fun z => s.f (t,z))=d.f₀ ∘ (fun z => F.backward (t,z)) := by
    funext z
    rw [F.transport_for_inverse hs.smooth_f hV,hs.initial_f]
    rfl
  rw [hrep]
  have hj := hcomp d.f₀ (fun z => F.backward (t,z)) hd.1 hback z
    (fun i hi hi' => (hdjet i (by omega) _).trans (by linarith)) (by
      intro i hi hi'
      have he : (fun w => F.reversePath t w t)=(fun w => F.backward (t,w)) := by
        funext w; exact F.reversePath_end t w
      have hl := hlow E B hE hB F T hT hb t ht t ⟨ht.1,le_rfl⟩ z i hi hi'
      rw [he] at hl
      exact hl.trans (by linarith))
  have hf := hdjet (n+1) le_rfl (F.backward (t,z))
  have hg := htop E B hE hB F T hT hb H hH hh t ht z
  refine hj.trans (mul_le_mul_of_nonneg_left (by gcongr) hC |>.trans ?_)
  nlinarith [mul_nonneg hC hH,mul_nonneg (mul_nonneg hC hD) hH]

end RVM
end

end OAI
end

theorem solution : type_of% @OAI.RVM.transported_derivative_tame_oai := @OAI.RVM.transported_derivative_tame_oai
