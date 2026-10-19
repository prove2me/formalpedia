-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.hardPairing_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:58:31.01273+00:00
-- url     : https://prove2.me/submissions/0cc43c83-4c98-4643-9db3-c01979b3ef3f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HardPairing.lean:L55-L85
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.hardPairing_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Theorems.Thm_OAI_TriangularHilbert_Heat_errorPairing_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_selectedSum_le_cubic
import Theorems.Thm_OAI_TriangularHilbert_Heat_weight_hasDerivAt_variance

-- ---- from OAI.Analysis.TriangularHilbert.SignedWindowScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_dilation {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (t : ℝ) :
    density (q*s) t = (Real.sqrt s)⁻¹ * density q (t/Real.sqrt s) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  have he : -(t/Real.sqrt s)^2/(2*q) = -t^2/(2*(q*s)) := by
    field_simp
    nlinarith [hsq]
  unfold density
  rw [show 2*Real.pi*(q*s)=s*(2*Real.pi*q) by ring,Real.sqrt_mul hs.le,he]
  simp only [mul_inv_rev]
  ring

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SignedCenter ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma continuousOn_signedKernel (t : ℝ) : ContinuousOn (fun s => signedKernel s t) (Set.Ioi 0) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have hs' : 0 < s := hs
  unfold signedKernel density
  fun_prop (disch := positivity)

lemma signedKernel_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    IntervalIntegrable (fun s => signedKernel s t / s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact ((continuousOn_signedKernel t).div continuousOn_id (fun s hs => ne_of_gt hs)).mono
    (fun s hs => ha.trans_le hs.1)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.DiscretePairing ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

lemma kernelPairing_eq (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) :
    kernelPairing A h u K = ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(K i j (u i+u j+u k):ℂ) := by
  simp only [kernelPairing,kernelOutput,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

lemma kernelPairing_add (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K L : ι → ι → ℝ → ℝ) :
    kernelPairing A h u (fun i j t => K i j t+L i j t) = kernelPairing A h u K+kernelPairing A h u L := by
  simp only [kernelPairing_eq,Complex.ofReal_add,mul_add,Finset.sum_add_distrib]

lemma kernelPairing_const_mul (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) (c : ℝ) :
    kernelPairing A h u (fun i j t => c*K i j t) = (c:ℂ)*kernelPairing A h u K := by
  simp only [kernelPairing_eq,Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma kernelPairing_smooth [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) :
    kernelPairing A h u (fun i j => smoothKernel (a i j) (b i j)) = selectedSum A h u a b := by
  rw [kernelPairing_eq]
  rfl
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SmoothFormula ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_three_hasDerivAt {s : ℝ} (hs : 0 < s) (t : ℝ) :
    HasDerivAt (fun s => density (3*s) t)
      ((1/2)*((t/(3*s))^2-(3*s)⁻¹)*density (3*s) t*3) s := by
  have hd := (weight_hasDerivAt_variance 1 t 0 (3*s) (by positivity)).comp s
    ((hasDerivAt_id s).const_mul 3)
  simpa only [weight,score,sub_zero,one_mul,mul_one,Function.comp_def] using hd

lemma scalePrimitive_hasDerivAt {s t : ℝ} (hs : 0 < s) (ht : t ≠ 0) :
    HasDerivAt (fun s => scalePrimitive s t) (signedKernel s t/s) s := by
  have hr := Real.hasDerivAt_sqrt hs.ne'
  have hq := ((hasDerivAt_const s (t^2/9)).div (hasDerivAt_id s) hs.ne').sub_const (1/3)
  have hd := ((((hr.mul hq).const_mul 2).mul (density_three_hasDerivAt hs t)).div_const t)
  convert! hd using 1
  unfold signedKernel
  dsimp
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hs.le]
  ring

lemma smoothKernel_eq_primitive {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    (∫ s in a..b, signedKernel s t/s) = scalePrimitive b t-scalePrimitive a t := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact scalePrimitive_hasDerivAt (ha.trans_le hs.1) ht
  · exact signedKernel_intervalIntegrable ha hab t

lemma scalePrimitive_profile {s t : ℝ} (hs : 0 < s) :
    scalePrimitive s t = (kernelConstant-kernelProfile (t/Real.sqrt s))/t := by
  have hd := density_dilation hs (by norm_num : 0 < (3:ℝ)) t
  have he : density 3 (t/Real.sqrt s) = Real.sqrt s*density (3*s) t := by
    rw [hd]
    field_simp
  unfold kernelProfile scalePrimitive
  rw [he]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

lemma smoothKernel_eq_profile {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) :
    (∫ s in a..b, signedKernel s t/s) =
      (kernelProfile (t/Real.sqrt a)-kernelProfile (t/Real.sqrt b))/t := by
  rw [smoothKernel_eq_primitive ha hab ht,scalePrimitive_profile (ha.trans_le hab),scalePrimitive_profile ha]
  ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HardPairing ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma hardKernel_decomposition {r R : ℝ} (hr : 0 < r) (hb : r ≤ R) (t : ℝ) :
    smoothKernel (r^2) (R^2) t = kernelConstant*hardKernel r R t+endpointError r t-endpointError R t := by
  have hR := hr.trans_le hb
  by_cases ht : t = 0
  · subst t
    simp [smoothKernel,signedKernel,hardKernel,endpointError]
  unfold smoothKernel
  rw [smoothKernel_eq_profile (sq_pos_of_pos hr) (by nlinarith) ht,Real.sqrt_sq hr.le,Real.sqrt_sq hR.le]
  unfold endpointError errorProfile hardKernel
  simp only [abs_div,abs_of_pos hr,abs_of_pos hR,lt_div_iff₀ hr,lt_div_iff₀ hR,one_mul]
  split_ifs <;> ring

lemma selectedSum_le_no_finset (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    ‖selectedSum A h (fun m => h*(m:ℤ)) (fun i j => (r i j)^2) (fun i j => (R i j)^2)‖ ≤
      selectedConstant*arrayCubic A h := by
  classical
  let S : Finset ℝ := insert (h^2) ((Finset.univ.image (fun p : D×D => (r p.1 p.2)^2)) ∪
    (Finset.univ.image (fun p : D×D => (R p.1 p.2)^2)))
  apply selectedSum_le_cubic D A _ _ (fun i j => by have hh' := hr i j; have hb' := hb i j; nlinarith) S
    (Finset.insert_nonempty _ _) ?_ ?_ hh ?_
  · intro i j
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩))
  · intro i j
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩))
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hs
    · rfl
    rcases Finset.mem_union.mp hs with hs|hs
    · rcases Finset.mem_image.mp hs with ⟨⟨i,j⟩,_,rfl⟩
      have hh' := hr i j
      nlinarith
    · rcases Finset.mem_image.mp hs with ⟨⟨i,j⟩,_,rfl⟩
      have hh' := (hr i j).trans (hb i j)
      nlinarith

lemma hardPairing_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    ‖kernelPairing A h (fun m => h*(m:ℤ)) (fun i j => hardKernel (r i j) (R i j))‖ ≤
      hardPairingConstant*arrayCubic A h := by
  classical
  let u : D → ℝ := fun m => h*(m:ℤ)
  have he : (kernelConstant:ℂ)*kernelPairing A h u (fun i j => hardKernel (r i j) (R i j)) =
      selectedSum A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)-
        kernelPairing A h u (fun i j => endpointError (r i j))+
        kernelPairing A h u (fun i j => endpointError (R i j)) := by
    have hk : (fun i j => smoothKernel ((r i j)^2) ((R i j)^2)) = (fun i j t =>
        kernelConstant*hardKernel (r i j) (R i j) t+endpointError (r i j) t+-1*endpointError (R i j) t) := by
      funext i j t
      convert hardKernel_decomposition (hh.trans_le (hr i j)) (hb i j) t using 1
      ring
    have hs := kernelPairing_smooth A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)
    rw [hk,kernelPairing_add,kernelPairing_add,kernelPairing_const_mul,kernelPairing_const_mul] at hs
    push_cast at hs
    linear_combination hs
  have hn := (norm_add_le (selectedSum A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)-
      kernelPairing A h u (fun i j => endpointError (r i j)))
      (kernelPairing A h u (fun i j => endpointError (R i j)))).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  rw [← he,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hn
  have h1 := selectedSum_le_no_finset D A hh r R hr hb
  have h2 := errorPairing_le D A hh r hr
  have h3 := errorPairing_le D A hh R (fun i j => (hr i j).trans (hb i j))
  have hden := abs_pos.mpr kernelConstant_ne_zero
  rw [hardPairingConstant,div_mul_eq_mul_div,le_div_iff₀ hden]
  dsimp [u] at hn
  nlinarith only [hn,h1,h2,h3]
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.hardPairing_le := @_root_.OAI.TriangularHilbert.Heat.hardPairing_le
