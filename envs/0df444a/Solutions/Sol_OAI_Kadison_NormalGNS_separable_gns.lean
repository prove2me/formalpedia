-- Prove2me | solution 1 for OAI.Kadison.NormalGNS.separable_gns
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:21:13.705308+00:00
-- url     : https://prove2.me/submissions/fed8776f-5b72-4c4e-99a7-713e1c412901

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C049

section
-- module Solutions.OAIQ039_CM.Commutator_WOTCompact
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace Pointwise

open Filter ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma isCompact_normBall {C : ℝ} (hC : 0≤C) : IsCompact (normBall (H:=H) C) := by
  classical
  apply isCompact_iff_ultrafilter_le_nhds.mpr
  intro ω hω
  let T : (H →WOT[ℂ] H) → H →L[ℂ] H := fun U => if ‖U.toCLM‖≤C then U.toCLM else 0
  have hT : ∀ U, ‖T U‖≤C := by
    intro U
    dsimp [T]
    split_ifs with h
    · exact h
    · simpa using hC
  obtain ⟨V,hV,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T C hC hT
  refine ⟨ofCLM V,hV,?_⟩
  apply (tendsto_iff_forall_inner_apply_tendsto (f:=id)).mpr
  intro x y
  have hh : Tendsto (fun U => inner ℂ y (T U x)) (ω : Filter (H →WOT[ℂ] H))
      (𝓝 (inner ℂ y (V x))) := by
    simpa only [RCLike.star_def,inner_conj_symm] using (hlim x y).star
  apply hh.congr'
  filter_upwards [Filter.le_principal_iff.mp hω] with U hU
  change inner ℂ y (T U x)=inner ℂ y (U x)
  change ‖U.toCLM‖≤C at hU
  dsimp [T]
  rw [ite_eq_left hU]
  rfl

omit [CompleteSpace H] in
lemma isClosed_commutant (S : Set (H →L[ℂ] H)) :
    IsClosed (commutant S : Set (H →WOT[ℂ] H)) := by
  change IsClosed {T | ∀ a∈S, ofCLM a*T=T*ofCLM a}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro _
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WOTBallSeparable
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma isClosed_vonNeumann (M : VonNeumannAlgebra H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM∈M} := by
  have he : {T : H →WOT[ℂ] H | T.toCLM∈M}=
      (commutant (Set.centralizer (M : Set (H →L[ℂ] H))) : Set (H →WOT[ℂ] H)) := by
    ext T
    change T.toCLM∈M.carrier ↔ ∀ a∈Set.centralizer (M : Set (H →L[ℂ] H)),ofCLM a*T=T*ofCLM a
    rw [←M.centralizer_centralizer']
    constructor
    · intro h a ha
      exact congrArg ofCLM (h a ha)
    · intro h a ha
      exact congrArg toCLM (h a ha)
  rw [he]
  exact isClosed_commutant _

lemma compact_algebraBall (M : VonNeumannAlgebra H) {C : ℝ} (hC : 0≤C) :
    CompactSpace (AlgebraBall M C) := by
  apply isCompact_iff_compactSpace.mp
  exact (isCompact_normBall hC).inter_left (isClosed_vonNeumann M)

theorem secondCountable_algebraBall [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) {C : ℝ} (hC : 0≤C) :
    SecondCountableTopology (AlgebraBall M C) := by
  classical
  let : CompactSpace (AlgebraBall M C) := compact_algebraBall M hC
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq H
  let f : AlgebraBall M C → (ℕ×ℕ → ℂ) := fun T ij => inner ℂ (v ij.1) (T.val (v ij.2))
  have hf : Continuous f := by
    apply continuous_pi
    intro ij
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val _ _
  have hi : Function.Injective f := by
    intro T S he
    apply Subtype.ext
    apply ContinuousLinearMapWOT.toCLM_injective
    apply ContinuousLinearMap.ext
    intro x
    have hcoeff (n m : ℕ) : inner ℂ (v n) (T.val.toCLM (v m))=
        inner ℂ (v n) (S.val.toCLM (v m)) := congrFun he (n,m)
    have hx (m : ℕ) : T.val.toCLM (v m)=S.val.toCLM (v m) :=
      hv.eq_of_inner_right ℂ (fun n => hcoeff n m)
    exact hv.induction_on x (isClosed_eq T.val.toCLM.continuous S.val.toCLM.continuous) hx
  exact (hf.isClosedEmbedding hi).isEmbedding.secondCountableTopology

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNSSeparable
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open Filter

open scoped InnerProductSpace Topology NNReal ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma continuous_ball_coefficient (hnormal : BoundedWOTContinuous M τ) (x : τ.GNS) :
    Continuous (fun a : AlgebraBall M 1 => inner ℂ x (algebraVector τ ⟨a.val.toCLM,a.property.1⟩)) := by
  rw [continuous_iff_continuousAt]
  intro b
  have ht := tendsto_gns M τ hnormal
    (fun a : AlgebraBall M 1 => (⟨a.val.toCLM,a.property.1⟩ : M))
    (⟨b.val.toCLM,b.property.1⟩ : M) 1 (fun a => a.property.2) b.property.2
    (l := 𝓝 b) (fun ξ η => ?_) x (vacuum τ)
  · simp only [left_vacuum] at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  · have hc := ContinuousLinearMapWOT.continuous_inner_apply
      (continuous_subtype_val : Continuous (fun a : AlgebraBall M 1 => a.val)) ξ η
    have hh := (hc.tendsto b).star
    simp only [RCLike.star_def,inner_conj_symm] at hh
    exact hh

theorem separable_gns_oai [TopologicalSpace.SeparableSpace H]
    (hnormal : BoundedWOTContinuous M τ) : TopologicalSpace.SeparableSpace τ.GNS := by
  classical
  let : SecondCountableTopology (AlgebraBall M 1) := secondCountable_algebraBall M zero_le_one
  let : Nonempty (AlgebraBall M 1) := ⟨⟨0,M.zero_mem,by simp⟩⟩
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq (AlgebraBall M 1)
  let v : ℕ → τ.GNS := fun n => algebraVector τ ⟨(a n).val.toCLM,(a n).property.1⟩
  let K : Submodule ℂ τ.GNS := Submodule.span ℂ (Set.range v)
  have hK : K.topologicalClosure=⊤ := by
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    have hv (n : ℕ) : inner ℂ x (v n)=0 := (K.mem_orthogonal' x).mp hx _
      (Submodule.subset_span (Set.mem_range_self n))
    have hball (b : AlgebraBall M 1) : inner ℂ x (algebraVector τ ⟨b.val.toCLM,b.property.1⟩)=0 := by
      exact ha.induction_on b (isClosed_eq (continuous_ball_coefficient M τ hnormal x) continuous_const) hv
    have hall (b : M) : inner ℂ x (algebraVector τ b)=0 := by
      by_cases hb : b=0
      · simp only [hb,map_zero,inner_zero_right]
      have hb' : (‖b‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
      let c : M := (‖b‖ : ℂ)⁻¹ • b
      have hn : ‖c‖≤1 := by
        dsimp only [c]
        rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg b)]
        exact le_of_eq (inv_mul_cancel₀ (norm_ne_zero_iff.mpr hb))
      have hc := hball ⟨ContinuousLinearMapWOT.ofCLM c,c.property,hn⟩
      have hbc : b=(‖b‖ : ℂ) • c := by
        dsimp only [c]
        rw [smul_smul,mul_inv_cancel₀ hb',one_smul]
      rw [hbc,map_smul,inner_smul_right,hc,mul_zero]
    have hx0 : x=0 := (algebraVector_dense τ).eq_of_inner_left ℂ
      (fun b => by simpa only [inner_zero_left] using hall b)
    simpa only [Submodule.mem_bot] using hx0
  have hs : TopologicalSpace.IsSeparable (K.topologicalClosure : Set τ.GNS) :=
    ((Set.countable_range v).isSeparable.span (R := ℂ)).closure
  rw [hK] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end Kadison.NormalGNS

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalGNS.separable_gns_oai.{u_1} := @OAI.Kadison.NormalGNS.separable_gns_oai.{u_1}
