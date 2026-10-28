-- Prove2me | solution 1 for OAI.Kadison.WOTDistance.exists_commutant_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:14:48.039277+00:00
-- url     : https://prove2.me/submissions/8d6e0e22-c1c4-47cd-a48d-5d8dc7cf4452

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C031
import Theorems.Thm_OAI_Kadison_WOTDistance_annihilator_bound
import Theorems.Thm_OAI_Kadison_WOTDistance_ball_functional_bound

section
-- module Solutions.OAIQ039_CM.Commutator_WOTCompact
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
lemma convex_normBall (C : ℝ) : Convex ℝ (normBall (H:=H) C) := by
  intro x hx y hy a b ha hb hab
  change ‖a • x.toCLM+b • y.toCLM‖≤C
  calc
    _ ≤ ‖a • x.toCLM‖+‖b • y.toCLM‖ := norm_add_le _ _
    _ = a*‖x.toCLM‖+b*‖y.toCLM‖ := by simp [norm_smul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*C+b*C := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = C := by rw [←add_mul,hab,one_mul]

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

lemma isClosed_commutant_add_ball (S : Set (H →L[ℂ] H)) {C : ℝ} (hC : 0≤C) :
    IsClosed ((commutant S : Set (H →WOT[ℂ] H))+normBall C) := by
  exact (isClosed_commutant S).add_right_of_isCompact (isCompact_normBall hC)

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ArvesonDistance
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Pointwise

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutant_membership (M : VonNeumannAlgebra H) (T : H →WOT[ℂ] H) :
    T∈commutant (M : Set (H →L[ℂ] H)) ↔ T.toCLM∈M.commutant := by
  change (∀ a∈M,ofCLM a*T=T*ofCLM a) ↔ _
  rw [VonNeumannAlgebra.mem_commutant_iff]
  constructor <;> intro h a ha
  · exact congrArg toCLM (h a ha)
  · apply toCLM_injective
    exact h a ha

theorem exists_commutant_approximation_oai (M : VonNeumannAlgebra H) (G : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hcb : AmplifiedBound M G c) :
    ∃ T : H →L[ℂ] H, T∈M.commutant ∧ ‖G-T‖ ≤ c := by
  classical
  let s := (commutant (M : Set (H →L[ℂ] H)) : Set (H →WOT[ℂ] H))+normBall c
  have hs0 : (0 : H →WOT[ℂ] H)∈s := by
    exact Set.mem_add.mpr ⟨0,(commutant _).zero_mem,0,by simpa [normBall] using hc,add_zero _⟩
  have hs : ofCLM G∈s := by
    by_contra hG
    have hsv : Convex ℝ s := ((commutant _).restrictScalars ℝ).convex.add (convex_normBall c)
    have hsc : IsClosed s := isClosed_commutant_add_ball _ hc
    obtain ⟨φ,u,hφ,hu⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜:=ℂ) hsv hsc hG
    have hu0 : 0<u := by simpa using hφ 0 hs0
    have hzero : ∀ T∈M.commutant,φ (ofCLM T)=0 := by
      intro T hT
      by_contra hn
      let z : ℂ := ((u+1 : ℝ) : ℂ)/φ (ofCLM T)
      have hz : z • ofCLM T∈s := by
        apply Set.mem_add.mpr
        refine ⟨z • ofCLM T, (commutant _).smul_mem z ?_,0,?_,add_zero _⟩
        · exact (commutant_membership M _).mpr hT
        · simpa [normBall] using hc
      have hh := hφ (z • ofCLM T) hz
      rw [map_smul,smul_eq_mul] at hh
      dsimp [z] at hh
      rw [div_mul_cancel₀ _ hn,Complex.ofReal_re] at hh
      linarith
    have hb : ∀ V∈normBall (H:=H) c,(φ V).re≤u := by
      intro V hV
      exact (hφ V (Set.mem_add.mpr ⟨0,(commutant _).zero_mem,V,hV,zero_add _⟩)).le
    have hnorm := annihilator_bound M G hc hcb φ hzero
    have hup : c*‖φ.comp ContinuousLinearMap.WOTofCLM‖≤u := by
      rcases hc.eq_or_lt with h|h
      · simp [←h,hu0.le]
      · exact ball_functional_bound φ h hu0.le hb
    change u < (φ (ofCLM G)).re at hu
    have hre := Complex.re_le_norm (φ (ofCLM G))
    linarith
  obtain ⟨T,hT,V,hV,hTV⟩ := Set.mem_add.mp hs
  refine ⟨T.toCLM,(commutant_membership M T).mp hT,?_⟩
  have hG : G-T.toCLM=V.toCLM := by
    have hh := congrArg toCLM hTV
    change T.toCLM+V.toCLM=G at hh
    rw [←hh,add_sub_cancel_left]
  rw [hG]
  exact hV

end Kadison.WOTDistance

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.WOTDistance.exists_commutant_approximation_oai.{u_1} := @OAI.Kadison.WOTDistance.exists_commutant_approximation_oai.{u_1}
