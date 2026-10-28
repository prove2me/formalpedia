-- Prove2me | solution 1 for OAI.Kadison.CyclicSpectral.stableUnitary_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:18:56.941593+00:00
-- url     : https://prove2.me/submissions/16359d1f-546e-4b46-99c4-55d378e2f495

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C035

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.InfiniteAmplification

variable {ι H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace H] [CompleteSpace G] in
lemma mapEquiv_intertwines (U : H ≃ₗᵢ[ℂ] G) (S : H →L[ℂ] H) (T : G →L[ℂ] G)
    (hU : ∀ x,U (S x)=T (U x)) (x : Space ι H) : mapEquiv U (map S x)=map T (mapEquiv U x) := by
  ext i
  exact hU (x i)

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_L2InfiniteSumCoordinates
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped InnerProductSpace Topology ENNReal

namespace Kadison.Decomposable

open InfiniteAmplification

attribute [local instance] OAI.l2InfiniteSumCoordinatesDecidableEq
variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma infiniteSumEquiv_single (i : ι) (f : Lp H 2 μ) :
    infiniteSumEquiv μ (lp.single 2 i f)=singleL μ i f := by
  classical
  exact IsHilbertSum.linearIsometryEquiv_symm_apply_single _ _

lemma evalL_infiniteSumEquiv (i : ι) (f : Space ι (Lp H 2 μ)) :
    evalL μ i (infiniteSumEquiv μ f)=f i := by
  apply ext_inner_left ℂ
  intro g
  rw [←inner_singleL,←infiniteSumEquiv_single]
  exact ((infiniteSumEquiv (H:=H) (ι:=ι) μ).inner_map_map
    (lp.single (E:=fun _ : ι => Lp H 2 μ) 2 i g) f).trans
      (lp.inner_single_left (𝕜:=ℂ) i g f)

variable [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

lemma scalarVectorMultiplier_ae (f : C(Ω,ℂ)) (v : Lp H 2 μ) :
    scalarVectorMultiplier μ f v=ᵐ[μ] fun x => f x • v x := operator_ae ..

omit [Countable ι] in
lemma evalL_scalarMultiplier (i : ι) (f : C(Ω,ℂ)) (v : Lp (Space ι H) 2 μ) :
    evalL μ i (scalarVectorMultiplier μ f v)=scalarVectorMultiplier μ f (evalL μ i v) := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i)
    (scalarVectorMultiplier μ f v),scalarVectorMultiplier_ae μ f v,
    scalarVectorMultiplier_ae μ f (evalL μ i v),
    ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) v] with x h₁ h₂ h₃ h₄
  change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp (scalarVectorMultiplier μ f v)) x=_
  rw [h₁,h₃]
  change (scalarVectorMultiplier μ f v) x i=f x • ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp v) x
  rw [h₂,h₄]
  rfl

lemma infiniteSumEquiv_scalar (f : C(Ω,ℂ)) (v : Space ι (Lp H 2 μ)) :
    infiniteSumEquiv μ (map (scalarVectorMultiplier μ f) v)=
      scalarVectorMultiplier μ f (infiniteSumEquiv μ v) := by
  apply sub_eq_zero.mp
  apply evalL_separates μ
  intro i
  rw [map_sub,evalL_infiniteSumEquiv,evalL_scalarMultiplier,evalL_infiniteSumEquiv]
  simp only [map_apply,sub_self]

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableSpectralUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

open InfiniteAmplification Decomposable

variable {Ω H G : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma stableUnitary_intertwines_oai (W : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G) (V : Lp ℂ 2 μ ≃ₗᵢ[ℂ] G)
    (S : H →L[ℂ] H) (T : G →L[ℂ] G) (f : C(Ω,ℂ))
    (hW : ∀ x,W (map S x)=map T (W x))
    (hV : ∀ x,V (scalarMultiplier μ f x)=T (V x)) (v : Space ℕ H) :
    stableUnitary μ W V (map S v)=scalarVectorMultiplier μ f (stableUnitary μ W V v) := by
  change infiniteSumEquiv μ (mapEquiv V.symm (W (map S v)))=_
  rw [hW]
  have he : ∀ x,V.symm (T x)=scalarMultiplier μ f (V.symm x) := by
    intro x
    apply V.injective
    rw [V.apply_symm_apply,hV,V.apply_symm_apply]
  rw [mapEquiv_intertwines V.symm _ _ he]
  exact infiniteSumEquiv_scalar μ f _

end Kadison.CyclicSpectral

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.CyclicSpectral.stableUnitary_intertwines_oai.{u_1, u_2, u_3} := @OAI.Kadison.CyclicSpectral.stableUnitary_intertwines_oai.{u_1, u_2, u_3}
