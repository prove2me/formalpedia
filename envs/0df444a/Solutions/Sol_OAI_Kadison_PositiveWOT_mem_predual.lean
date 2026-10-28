-- Prove2me | solution 1 for OAI.Kadison.PositiveWOT.mem_predual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:23:28.677924+00:00
-- url     : https://prove2.me/submissions/8e949a9b-42d4-4842-9712-2fc623d8db09

import Mathlib
import Definitions.Def_OAIQ039C040
import Theorems.Thm_OAI_Kadison_PositiveWOT_positive_strong_null

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStrongTest
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison.FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma strong_null_of_dense_tests (M : VonNeumannAlgebra H) (v : ℕ → H) (hv : DenseRange v)
    (T : ℕ → M) (hT : ∀ n,‖T n‖≤1)
    (ht : ∀ n,∀ j : Fin n,‖(T n : H →L[ℂ] H) (v j)‖≤1/((n:ℝ)+1)) :
    ∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  intro x
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := hv.exists_dist_lt x (by positivity : (0:ℝ)<ε/3)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const (by positivity : (0:ℝ)<ε/3))
  refine ⟨max N (j+1),?_⟩
  intro n hn
  have hnN : N≤n := le_trans (le_max_left _ _) hn
  have hjn : j<n := by omega
  have he : (T n : H →L[ℂ] H) x=(T n : H →L[ℂ] H) (x-v j)+(T n : H →L[ℂ] H) (v j) := by simp
  have hb : ‖(T n : H →L[ℂ] H) (x-v j)‖≤‖x-v j‖ := by
    calc
      _ ≤ ‖T n‖*‖x-v j‖ := (T n : H →L[ℂ] H).le_opNorm _
      _ ≤ 1*‖x-v j‖ := mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)
      _ = _ := one_mul _
  have hd : ‖x-v j‖<ε/3 := by simpa only [dist_eq_norm] using hj
  have hb2 := ht n ⟨j,hjn⟩
  have hh : ‖(T n : H →L[ℂ] H) x‖<ε := by
    rw [he]
    have hh := norm_add_le ((T n : H →L[ℂ] H) (x-v j)) ((T n : H →L[ℂ] H) (v j))
    have hsmall := hN n hnN
    change ‖(T n : H →L[ℂ] H) (v j)‖≤1/((n:ℝ)+1) at hb2
    linarith
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using hh

theorem exists_test (M : VonNeumannAlgebra H) (v : ℕ → H) (hv : DenseRange v)
    (f : StrongDual ℂ M)
    (hf : ∀ T : ℕ → M,(∀ n,‖T n‖≤1) →
      (∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0)) →
      Tendsto (fun n => f (T n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ a : M,‖a‖≤1 → (∀ j : Fin N,‖(a : H →L[ℂ] H) (v j)‖≤1/((N:ℝ)+1)) →
      ‖f a‖≤ε := by
  by_contra h
  push Not at h
  choose T hT ht hlarge using h
  have hlim := (hf T hT (strong_null_of_dense_tests M v hv T hT ht)).norm
  have hsmall : ∀ᶠ n in atTop,‖f (T n)‖<ε := by
    apply hlim.eventually_lt_const
    simpa only [norm_zero] using hε
  obtain ⟨n,hn⟩ := hsmall.exists
  exact (hlarge n).not_ge hn.le

end Kadison.FiniteStrongTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestHahnBanach
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FiniteTestHahnBanach

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma scaled_test_bound (f : StrongDual ℂ E) (A : E →L[ℂ] F)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (h : ∀ x : E,‖x‖≤1 → ‖A x‖≤δ → ‖f x‖≤ε) (x : E) :
    ‖f x‖≤ε*max ‖x‖ (‖A x‖/δ) := by
  by_cases hx : x=0
  · subst x
    simp only [map_zero,norm_zero]
    exact mul_nonneg hε.le (le_max_left _ _)
  let r : ℝ := max ‖x‖ (‖A x‖/δ)
  have hr : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr hx) (le_max_left _ _)
  have hxr : ‖x‖ ≤ r := le_max_left _ _
  have har : ‖A x‖≤δ*r := by
    have hh : ‖A x‖/δ ≤ r := le_max_right _ _
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  have hc : ‖((r⁻¹:ℝ):ℂ)‖=r⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  have hx1 : ‖((r⁻¹:ℝ):ℂ) • x‖≤1 := by
    rw [norm_smul,hc]
    calc
      _ ≤ r⁻¹*r := mul_le_mul_of_nonneg_left hxr (le_of_lt (inv_pos.mpr hr))
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have ha1 : ‖A (((r⁻¹:ℝ):ℂ) • x)‖≤δ := by
    rw [map_smul,norm_smul,hc]
    calc
      _ ≤ r⁻¹*(δ*r) := mul_le_mul_of_nonneg_left har (le_of_lt (inv_pos.mpr hr))
      _ = δ := by field_simp
  have hh := h (((r⁻¹:ℝ):ℂ) • x) hx1 ha1
  rw [map_smul,norm_smul,hc] at hh
  have ht := mul_le_mul_of_nonneg_left hh hr.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hr.ne',one_mul,mul_comm] using ht

theorem exists_approx_comp (f : StrongDual ℂ E) (A : E →L[ℂ] F)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (h : ∀ x : E,‖x‖≤1 → ‖A x‖≤δ → ‖f x‖≤ε) :
    ∃ ψ : StrongDual ℂ F,‖f-ψ.comp A‖≤ε := by
  let g : E →L[ℂ] E×F := ((ε:ℂ) • ContinuousLinearMap.id ℂ E).prod (((ε/δ:ℝ):ℂ) • A)
  have hg (x : E) : g x=((ε:ℂ) • x,((ε/δ:ℝ):ℂ) • A x) := rfl
  have hgnorm (x : E) : ‖g x‖=ε*max ‖x‖ (‖A x‖/δ) := by
    rw [hg,Prod.norm_def]
    simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hε,abs_of_pos (div_pos hε hδ)]
    rw [mul_max_of_nonneg _ _ hε.le]
    congr 1
    ring
  have hgi : Function.Injective g := by
    intro x y hxy
    have hh : (ε:ℂ) • x=(ε:ℂ) • y := congrArg Prod.fst hxy
    exact (smul_right_injective E (by exact_mod_cast hε.ne')) hh
  let e := LinearEquiv.ofInjective g.toLinearMap hgi
  have heb (y : g.toLinearMap.range) : ‖f (e.symm y)‖≤‖y‖ := by
    have hh := scaled_test_bound f A hε hδ h (e.symm y)
    rw [←hgnorm] at hh
    have he : g (e.symm y)=(y:E×F) := LinearEquiv.ofInjective_symm_apply g.toLinearMap y
    rw [he] at hh
    exact hh
  let l : StrongDual ℂ g.toLinearMap.range :=
    (f.toLinearMap.comp e.symm.toLinearMap).mkContinuous 1 (by
      intro y
      change ‖f (e.symm y)‖≤1*‖y‖
      simpa only [one_mul] using heb y)
  have hln : ‖l‖≤1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  obtain ⟨G,hGe,hGn⟩ := exists_extension_norm_eq g.toLinearMap.range l
  have hG : ‖G‖≤1 := hGn.trans_le hln
  have hGg (x : E) : G (g x)=f x := by
    have hh := hGe (e x)
    change G (g x)=f (e.symm (e x)) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  let ψ : StrongDual ℂ F := G.comp (((ε/δ:ℝ):ℂ) • ContinuousLinearMap.inr ℂ E F)
  refine ⟨ψ,?_⟩
  apply (f-ψ.comp A).opNorm_le_bound hε.le
  intro x
  have he : (f-ψ.comp A) x=G ((ε:ℂ) • x,0) := by
    change f x-G (((ε/δ:ℝ):ℂ) • ((0:E),A x))=_
    rw [Prod.smul_mk,smul_zero]
    rw [←hGg x,hg,←map_sub]
    congr 1
    simp
  rw [he]
  calc
    _ ≤ ‖G‖*‖((ε:ℂ) • x,(0:F))‖ := G.le_opNorm _
    _ ≤ 1*‖((ε:ℂ) • x,(0:F))‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
    _ = ε*‖x‖ := by
      simp [Prod.norm_def,norm_smul,abs_of_pos hε,mul_nonneg hε.le (norm_nonneg x)]

end Kadison.FiniteTestHahnBanach

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalPredual
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped Topology InnerProductSpace

namespace Kadison.NormalPredual

open FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_closure_of_strong_null (M : VonNeumannAlgebra H) (v : ℕ → H)
    (hv : DenseRange v) (f : StrongDual ℂ M)
    (hf : ∀ T : ℕ → M,(∀ n,‖T n‖≤1) →
      (∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0)) →
      Tendsto (fun n => f (T n)) atTop (𝓝 0)) :
    f∈closure (finiteTests M v) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_test M v hv f hf (ε/2) (by positivity)
  obtain ⟨ψ,hψ⟩ := FiniteTestHahnBanach.exists_approx_comp f (testMap M v N)
    (by positivity : (0:ℝ)<ε/2) (by positivity : (0:ℝ)<1/((N:ℝ)+1)) (by
      intro a ha htest
      apply hN a ha
      intro j
      exact (PiLp.norm_apply_le (testMap M v N a) j).trans htest)
  let y := (InnerProductSpace.toDual ℂ (PiLp 2 (fun _ : Fin N => H))).symm ψ
  have he : coefficient M v N y=ψ.comp (testMap M v N) := by
    apply ContinuousLinearMap.ext
    intro a
    change inner ℂ ((InnerProductSpace.toDual ℂ (PiLp 2 (fun _ : Fin N => H))).symm ψ)
      (testMap M v N a)=ψ (testMap M v N a)
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨coefficient M v N y,Set.mem_iUnion.mpr ⟨N,Set.mem_range_self y⟩,?_⟩
  rw [he,dist_eq_norm]
  exact hψ.trans_lt (by linarith)

end Kadison.NormalPredual

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionNormalStrong
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma functional_cauchySchwarz (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (a : M) :
    ‖f a‖^2≤(f 1).re*(f (star a*a)).re := by
  have hi := norm_inner_le_norm (𝕜:=ℂ) (f.toPreGNS 1) (f.toPreGNS a)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
  have he (b : M) : ‖f.toPreGNS b‖^2=(f (star b*b)).re := by
    rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
    rfl
  rw [mul_pow,he 1,he a] at hs
  simpa only [f.preGNS_inner_def,f.ofPreGNS_toPreGNS,star_one,one_mul] using hs

theorem contraction_strong_null [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
    (T : ℕ → M) (hT : ∀ n,‖T n‖≤1)
    (ht : ∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0)) :
    Tendsto (fun n => f (T n)) atTop (𝓝 0) := by
  have hpos (n : ℕ) : (0:M)≤ star (T n)*T n := star_mul_self_nonneg _
  have hnorm (n : ℕ) : ‖star (T n)*T n‖≤1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (T n),hT n]
  have hone (n : ℕ) : star (T n)*T n≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpos n)).mp (hnorm n)
  have hs (x : H) : Tendsto (fun n => ((star (T n)*T n : M) : H →L[ℂ] H) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ ((ht x).norm.trans (by simp))
    intro n
    change ‖(star (T n) : H →L[ℂ] H) ((T n : H →L[ℂ] H) x)‖≤_
    calc
      _ ≤ ‖(star (T n) : H →L[ℂ] H)‖*‖(T n : H →L[ℂ] H) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*‖(T n : H →L[ℂ] H) x‖ := mul_le_mul_of_nonneg_right
        (by simpa using hT n) (norm_nonneg _)
      _ = _ := one_mul _
  have hlim := positive_strong_null M f hf (fun n => star (T n)*T n) hpos hone hs
  have hre : Tendsto (fun n => (f 1).re*(f (star (T n)*T n)).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.zero_re,mul_zero] using
      (Complex.continuous_re.tendsto 0 |>.comp hlim).const_mul (f 1).re
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hre.eventually_lt_const (sq_pos_of_pos hε))
  refine ⟨N,?_⟩
  intro n hn
  have hc := functional_cauchySchwarz M f (T n)
  have hh := hN n hn
  have hl : ‖f (T n)‖<ε := by nlinarith [norm_nonneg (f (T n))]
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using hl

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionNormalBridge
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_predual_oai [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f) :
    strongFunctional M f∈closure (NormalPredual.finiteTests M (TopologicalSpace.denseSeq H)) := by
  apply NormalPredual.mem_closure_of_strong_null M (TopologicalSpace.denseSeq H)
    (TopologicalSpace.denseRange_denseSeq H)
  intro T hT ht
  exact contraction_strong_null M f hf T hT ht

end Kadison.PositiveWOT

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PositiveWOT.mem_predual_oai.{u_1} := @OAI.Kadison.PositiveWOT.mem_predual_oai.{u_1}
