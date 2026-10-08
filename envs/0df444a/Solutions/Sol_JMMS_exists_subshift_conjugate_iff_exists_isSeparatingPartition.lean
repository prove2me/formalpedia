-- Prove2me | solution 1 for JMMS.exists_subshift_conjugate_iff_exists_isSeparatingPartition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T14:50:12.501987+00:00
-- url     : https://prove2.me/submissions/87d48fe7-dafe-4c21-8d6d-bbc938c2d2af

import Mathlib
import Definitions.Def_CantorSystems

section

open CantorSystems

namespace JMMS

namespace IETL510

variable {Γ X : Type*} [AddGroup Γ] [TopologicalSpace X] [AddAction Γ X]

/-- A map to a discrete space with clopen fibres is continuous. -/
lemma continuous_of_isClopenPartition {k : ℕ} {p : X → Fin k} (hp : IsClopenPartition p) :
    Continuous p := by
  rw [continuous_discrete_rng]
  intro i
  exact (hp i).isOpen

/-- The coding map `x ↦ (δ ↦ p (δ +ᵥ x))`. -/
def code {k : ℕ} (p : X → Fin k) (x : X) : Γ → Fin k := fun δ => p (δ +ᵥ x)

omit [TopologicalSpace X] in
lemma code_vadd {k : ℕ} (p : X → Fin k) (γ : Γ) (x : X) :
    code p (γ +ᵥ x) = shift γ (code p x) := by
  funext δ
  simp [code, add_vadd]

lemma forward {k : ℕ} (S : Subshift Γ (Fin k)) (e : X ≃ₜ S)
    (he : ∀ (γ : Γ) (x : X), e (γ +ᵥ x) = γ +ᵥ e x) :
    IsClopenPartition (fun x => ((e x : S) : Γ → Fin k) 0) ∧
      IsSeparatingPartition Γ (fun x => ((e x : S) : Γ → Fin k) 0) := by
  refine ⟨fun i => ?_, fun x y hxy => ?_⟩
  · have hc : Continuous (fun x => ((e x : S) : Γ → Fin k) 0) :=
      (continuous_apply 0).comp (continuous_subtype_val.comp e.continuous)
    exact (isClopen_discrete {i}).preimage hc
  · apply e.injective
    apply Subtype.ext
    funext γ
    have h := hxy γ
    simp only [he, Subshift.coe_vadd, shift_apply, zero_add] at h
    exact h

end IETL510

open IETL510 in
theorem chk_exists_subshift_conjugate_iff_exists_isSeparatingPartition
    {Γ X : Type*} [AddGroup Γ] [TopologicalSpace X] [AddAction Γ X] [ContinuousConstVAdd Γ X]
    (hX : IsCantorSpace X) :
    (∃ k : ℕ, ∃ S : Subshift Γ (Fin k), ∃ e : X ≃ₜ S,
      ∀ (γ : Γ) (x : X), e (γ +ᵥ x) = γ +ᵥ e x) ↔
    ∃ k : ℕ, ∃ p : X → Fin k, IsClopenPartition p ∧ IsSeparatingPartition Γ p := by
  constructor
  · rintro ⟨k, S, e, he⟩
    exact ⟨k, _, forward S e he⟩
  · rintro ⟨k, p, hp, hsep⟩
    have : CompactSpace X := hX.2.1
    have hpc := continuous_of_isClopenPartition hp
    have hcont : Continuous (code (Γ := Γ) p) :=
      continuous_pi fun δ => hpc.comp (continuous_const_vadd δ)
    have hinj : Function.Injective (code (Γ := Γ) p) := fun x y h =>
      hsep x y fun γ => congrFun h γ
    let S : Subshift Γ (Fin k) :=
      ⟨Set.range (code (Γ := Γ) p),
        ⟨(isCompact_range hcont).isClosed, by
          rintro γ _ ⟨x, rfl⟩
          exact ⟨γ +ᵥ x, code_vadd p γ x⟩⟩⟩
    let f : X → S := fun x => ⟨code p x, ⟨x, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y h => hinj (congrArg Subtype.val h), ?_⟩
      rintro ⟨_, ⟨x, rfl⟩⟩
      exact ⟨x, rfl⟩
    have hfc : Continuous f := hcont.subtype_mk _
    refine ⟨k, S, hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf), ?_⟩
    intro γ x
    apply Subtype.ext
    exact code_vadd p γ x


end JMMS
end

open CantorSystems
theorem solution
    {Γ X : Type*} [AddGroup Γ] [TopologicalSpace X] [AddAction Γ X] [ContinuousConstVAdd Γ X]
    (hX : IsCantorSpace X) :
    (∃ k : ℕ, ∃ S : Subshift Γ (Fin k), ∃ e : X ≃ₜ S,
      ∀ (γ : Γ) (x : X), e (γ +ᵥ x) = γ +ᵥ e x) ↔
    ∃ k : ℕ, ∃ p : X → Fin k, IsClopenPartition p ∧ IsSeparatingPartition Γ p :=
  JMMS.chk_exists_subshift_conjugate_iff_exists_isSeparatingPartition hX
