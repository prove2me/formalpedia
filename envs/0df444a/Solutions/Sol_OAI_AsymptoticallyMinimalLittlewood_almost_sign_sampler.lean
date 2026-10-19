-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.almost_sign_sampler
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:05:56.561699+00:00
-- url     : https://prove2.me/submissions/868ef8d5-cbe5-43b5-864e-cb492c05b742

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/AlmostSign.lean:L10-L107
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.almost_sign_sampler. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_exists_auxiliary_packet
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_signed_interval_packing_general
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_sample_packed

-- ---- from OAI.Analysis.Littlewood.BlockSampling ----
namespace OAI

universe uP uJ uI

namespace AsymptoticallyMinimalLittlewood.Cutoff
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology ContDiff

end
end AsymptoticallyMinimalLittlewood.Cutoff

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators ComplexConjugate
open Complex UnitAddTorus
namespace Sampling
open QuadraticTail

lemma signed_fourier_sum {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (a : I → J → ℤ) (c : I → ℂ) (y : J → UnitAddCircle) :
    (∑ ei : Bool × I, (if ei.1 then c ei.2 else conj (c ei.2))*
      mFourier (if ei.1 then a ei.2 else -a ei.2) y)=
      (∑ i, c i*mFourier (a i) y)+conj (∑ i, c i*mFourier (a i) y) := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,ite_true,Bool.false_eq_true,
    ite_false,mFourier_neg,map_sum,map_mul]

end Sampling
end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
-- [generator] trimmed: open MeasureTheory Filter Complex QuadraticTail UnitAddTorus Packing Cutoff
open MeasureTheory Filter Complex QuadraticTail UnitAddTorus Packing

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- from OAI.Analysis.Littlewood.AlmostSign ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex UnitAddTorus

/-- The almost-sign sampling conclusion from the auxiliary packet and its packed
signed curvature intervals. Every datum is fixed before the variable N. -/
theorem almost_sign_sampler {δ : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20) :
    ∃ X : (N : ℕ) → Fin N → ℝ, ∃ L C : ℝ,
      0≤C ∧ 1-7*δ≤L ∧
      (∀ N : ℕ, 1≤N → ∀ k, |X N k|≤1) ∧
      Tendsto (fun N : ℕ ↦ (∑ k : Fin N, (X N k)^2)/(N : ℝ)) atTop (𝓝 L) ∧
      ∀ N : ℕ, 1≤N → ∀ t∈Set.Icc (0:ℝ) 1,
        ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N, (X N k : ℂ)*realPhase (2*Real.pi*t*k)‖≤
          Real.sqrt ((1+δ)^3/(1-δ))+C/N := by
  classical
  obtain ⟨P⟩ := Auxiliary.exists_auxiliary_packet hδ hδ20
  let D := P.data
  let a := D.frequency
  let c := D.coefficient
  let v := D.velocity
  let lam (i : P.I) := ∑ j, (a i j : ℝ)*v j
  have hlam0 (i : P.I) : lam i≠0 := D.curvature i
  have hw : 2*∑ i, |lam i|<1 := D.width
  obtain ⟨H,hH,θ,hθ⟩ := Packing.signed_interval_packing_general a D.nonzero
    (fun i j hij t ↦ D.nonparallel j i hij.symm t) (fun i ↦ |lam i|)
    (fun i ↦ abs_pos.mpr (hlam0 i)) hw
  have hθlift (h : Fin H) (j : P.J) : ∃ t : ℝ, (t : UnitAddCircle)=θ h j :=
    QuotientAddGroup.mk_surjective (θ h j)
  choose θr hθr using hθlift
  let A (ei : Bool × P.I) := if ei.1 then a ei.2 else -a ei.2
  let Cc (ei : Bool × P.I) := if ei.1 then c ei.2 else conj (c ei.2)
  have hal (ei : Bool × P.I) : |∑ j, (A ei j : ℝ)*v j|=|lam ei.2| := by
    rcases ei with ⟨e,i⟩
    cases e <;> simp [A,lam,Finset.sum_neg_distrib]
  have hcn (ei : Bool × P.I) : ‖Cc ei‖=‖c ei.2‖ := by
    rcases ei with ⟨e,i⟩
    cases e <;> simp [Cc]
  have henergy : (∑ ei : Bool × P.I, ‖Cc ei‖^2)=2*∑ i, ‖c i‖^2 := by
    simp only [hcn,Fintype.sum_prod_type,Fintype.sum_bool]
    ring
  have hfourier (y : P.J → UnitAddCircle) :
      (∑ ei, Cc ei*mFourier (A ei) y)=
        (∑ i, c i*mFourier (a i) y)+conj (∑ i, c i*mFourier (a i) y) :=
    Sampling.signed_fourier_sum a c y
  have hreal (y) : (∑ ei, Cc ei*mFourier (A ei) y).im=0 := by
    rw [hfourier]
    simp only [Complex.add_im,Complex.conj_im,add_neg_cancel]
  have hbound (y) : ‖∑ ei, Cc ei*mFourier (A ei) y‖≤1 := by
    rw [hfourier]
    exact D.bounded y
  have hlam (ei : Bool × P.I) : (∑ j, (A ei j : ℝ)*v j)≠0 := by
    have hh : 0 < |∑ j, (A ei j : ℝ)*v j| := by rw [hal]; exact abs_pos.mpr (hlam0 ei.2)
    exact abs_pos.mp hh
  have hwidth (ei : Bool × P.I) : |∑ j, (A ei j : ℝ)*v j|/(H : ℝ)<1 := by
    rw [hal]
    have hh := Finset.single_le_sum (fun i (_ : i∈Finset.univ) ↦ abs_nonneg (lam i)) (Finset.mem_univ ei.2)
    have hHr : (1:ℝ)≤H := by exact_mod_cast hH
    exact lt_of_le_of_lt (div_le_self (abs_nonneg _) hHr) (by linarith)
  have hlift (h : Fin H) (ei : Bool × P.I) :
      (((∑ j, (A ei j : ℝ)*θr h j : ℝ)) : UnitAddCircle)=
        Packing.signedCircle ei.1 (∑ j, a ei.2 j • θ h j) := by
    rcases ei with ⟨e,i⟩
    have hh : (((∑ j, (a i j : ℝ)*θr h j : ℝ)) : UnitAddCircle)=
        ∑ j, a i j • θ h j := by
      change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))) (∑ j, (a i j : ℝ)*θr h j)=_
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← zsmul_eq_mul,map_zsmul]
      change a i j • (θr h j : UnitAddCircle)=_
      rw [hθr]
    cases e <;> simp [A,Packing.signedCircle,Finset.sum_neg_distrib,hh]
  have hpack (h h' : Fin H) (ei ei' : Bool × P.I) (hne : (h,ei)≠(h',ei')) :
      Disjoint (Packing.circleInterval (((∑ j, (A ei j : ℝ)*θr h j : ℝ)) : UnitAddCircle)
        (|∑ j, (A ei j : ℝ)*v j|/H))
      (Packing.circleInterval (((∑ j, (A ei' j : ℝ)*θr h' j : ℝ)) : UnitAddCircle)
        (|∑ j, (A ei' j : ℝ)*v j|/H)) := by
    rw [hlift,hlift,hal,hal]
    apply hθ ei.1 ei'.1 ei.2 ei'.2 h h'
    intro he
    have he1 := congrArg (fun x : Bool × P.I × Fin H ↦ x.1) he
    have he2 := congrArg (fun x : Bool × P.I × Fin H ↦ x.2.1) he
    have he3 := congrArg (fun x : Bool × P.I × Fin H ↦ x.2.2) he
    exact hne (Prod.ext he3 (Prod.ext he1 he2))
  let K := Real.sqrt ((1+δ)^3/(1-δ))
  have hδ1 : δ<1 := by linarith
  have hbudget : 0≤(1+δ)^3/(1-δ) := by positivity
  have hc (ei : Bool × P.I) : ‖Cc ei‖/Real.sqrt |∑ j, (A ei j : ℝ)*v j|≤K := by
    rw [hal,hcn]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (abs_pos.mpr (hlam0 ei.2)))).mpr
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (abs_nonneg _),show K^2=(1+δ)^3/(1-δ) by exact Real.sq_sqrt hbudget]
    exact D.size ei.2
  obtain ⟨X,L,C,hC,hL,hX,hE,hmax⟩ := Sampling.sample_packed A Cc v hH θr
    hreal hbound hlam hwidth hpack (Real.sqrt_nonneg _) hδ hc
  refine ⟨X,L,C,hC,?_,hX,hE,hmax⟩
  rw [henergy] at hL
  have he := mul_le_mul_of_nonneg_left D.energy (show 0≤1-δ by linarith)
  have hn : 1-7*δ≤(1-δ)*(1-3*δ)^2 := by
    have hp : 0≤δ^2*(15-9*δ) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  exact hn.trans (he.trans hL)

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex UnitAddTorus


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.almost_sign_sampler := @_root_.OAI.AsymptoticallyMinimalLittlewood.almost_sign_sampler
