-- Prove2me | solution 1 for HardyCausaloid.eq35_conditional_ratio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T20:06:58.84796+00:00
-- url     : https://prove2.me/submissions/3a47b5d8-be65-4b8b-be6c-4ba6027507bb

import Definitions.Def_HardyCausaloid_Conditional
import Theorems.Thm_HardyCausaloid_fiducial_spanning_states

namespace HardyCausaloid

private theorem summable_from_states {ι B S : Type*} [Fintype ι]
    (p : S → ι → ℝ) (hspan : Submodule.span ℝ (Set.range p) = ⊤)
    (v : B → ι → ℝ) (he : ∀ s, Summable fun b => v b ⬝ᵥ p s) : Summable v := by
  classical
  let U : Submodule ℝ (ι → ℝ) :=
    { carrier := {x | Summable fun b => v b ⬝ᵥ x}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        simpa only [Set.mem_ofPred_eq, dotProduct_add] using hx.add hy
      smul_mem' := fun a x hx => by
        simpa only [Set.mem_ofPred_eq, dotProduct_smul, smul_eq_mul] using hx.mul_left a }
  have sub : Submodule.span ℝ (Set.range p) ≤ U := Submodule.span_le.mpr (by
    rintro _ ⟨s, rfl⟩
    exact he s)
  rw [hspan] at sub
  apply Pi.summable.mpr
  intro i
  have h : Summable fun b => v b ⬝ᵥ Pi.single i 1 :=
    sub (show Pi.single i (1 : ℝ) ∈ (⊤ : Submodule ℝ (ι → ℝ)) from trivial)
  simpa using h

private theorem tsum_pairing {ι B : Type*} [Fintype ι] (v : B → ι → ℝ)
    (hv : Summable v) (x : ι → ℝ) :
    (∑' b, v b ⬝ᵥ x) = (∑' b, v b) ⬝ᵥ x := by
  exact (hasSum_sum fun i (_ : i ∈ Finset.univ) =>
    ((Pi.hasSum.mp hv.hasSum) i).mul_right (x i)).tsum_eq

variable {X : Type*} {Setting : X → Type*} {Outcome : (x : X) → Setting x → Type*}
  [DecidableEq X]

private theorem regional_state_span (M : Model Setting Outcome) (C : Causaloid Setting Outcome)
    (O : Finset X)
    (h : Submodule.span ℝ (Set.range (stateVec (regionTable M O) (C.fidSet O))) = ⊤) :
    Submodule.span ℝ (Set.range (C.state M O)) = ⊤ := by
  let e : C.ΩC O ≃ C.fidSet O := Finset.equivMap ⟨C.embed O, C.embed_injective O⟩ _
  let f : (C.fidSet O → ℝ) →ₗ[ℝ] (C.ΩC O → ℝ) := LinearMap.pi fun i => LinearMap.proj (e i)
  have hf : Function.Surjective f := by
    intro w
    refine ⟨fun i => w (e.symm i), funext fun i => ?_⟩
    change w (e.symm (e i)) = w i
    simp
  change Submodule.span ℝ (Set.range (f ∘ stateVec (regionTable M O) (C.fidSet O))) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

private theorem scalar_outcome_summable (M : Model Setting Outcome)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.val) (base : ∀ x : O₂, Outcome x.val (F₂ x))
    (s : ∀ x, Label Setting Outcome x) :
    Summable (fun β : ∀ x : O₂, Outcome x.val (F₂ x) =>
      regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β)) s) := by
  classical
  let total (β : ∀ x : O₂, Outcome x.val (F₂ x)) :=
    glue (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β)) s
  let F x := (total base x).1
  have hF β x : (total β x).1 = F x := by
    by_cases hu : x ∈ O₁ ∪ O₂ <;> by_cases ha : x ∈ O₁ <;>
      simp only [F, total, glue, joinLab, labOf, hu, ha, ↓reduceDIte]
  let out (β : ∀ x : O₂, Outcome x.val (F₂ x)) (x : X) : Outcome x (F x) :=
    (hF β x) ▸ (total β x).2
  have labels β x : (⟨F x, out β x⟩ : Label Setting Outcome x) = total β x := by
    refine Sigma.ext ?_ ?_
    · exact (hF β x).symm
    · exact eqRec_heq _ _
  have onTwo β (x : O₂) : total β x.val = ⟨F₂ x, β x⟩ := by
    have ha : x.val ∉ O₁ := fun hx => Finset.disjoint_left.mp hO hx x.property
    have hu := Finset.mem_union_right O₁ x.property
    simp [total, glue, joinLab, labOf, hu, ha]
  have inj : Function.Injective out := by
    intro β γ h
    funext x
    have hl : total β x.val = total γ x.val :=
      (labels β x.val).symm.trans ((congrArg (Sigma.mk (F x.val)) (congrFun h x.val)).trans (labels γ x.val))
    rw [onTwo, onTwo] at hl
    exact eq_of_heq (Sigma.mk.inj_iff.mp hl).2
  have hs := (M.hasSum_prob F).summable.comp_injective inj
  apply hs.congr
  intro β
  change M.prob F (out β) = M.P (total β)
  change M.P (fun x => ⟨F x, out β x⟩) = _
  rw [show (fun x => (⟨F x, out β x⟩ : Label Setting Outcome x)) = total β from funext (labels β)]

end HardyCausaloid

open HardyCausaloid

theorem solution {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (C : Causaloid Setting Outcome) (hC : IsCausaloidOf C M)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) :
    Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
      C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂))) ∧
    (∀ s, Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
      regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂)) s)) ∧
    (∀ s, condNum M α₁ F₂ Y₂ s = condA C α₁ F₂ Y₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) ∧
    (∀ s, condDen M α₁ F₂ s = condB C α₁ F₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) := by
  have hsFid := (fiducial_spanning_states _ _ (hC.region_fiducial (O₁ ∪ O₂))).1
  classical
  let O := O₁ ∪ O₂
  let lab := fun β : ∀ x : O₂, Outcome x.val (F₂ x) => joinLab α₁ (labOf F₂ β)
  let v := fun β => C.r O (lab β)
  have hs := scalar_outcome_summable M hO α₁ F₂ Y₂
  have hp := regional_state_span M C O hsFid
  have hv : Summable v := summable_from_states (C.state M O) hp v fun s =>
    (hs s).congr fun β => hC.region_eq O (lab β) s
  refine ⟨hv, hs, fun s => hC.region_eq O (lab Y₂) s, ?_⟩
  intro s
  calc
    condDen M α₁ F₂ s = ∑' β, v β ⬝ᵥ C.state M O s := tsum_congr fun β => hC.region_eq O (lab β) s
    _ = _ := tsum_pairing v hv _
