-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:58.689224+00:00
-- url     : https://prove2.me/submissions/b99ecbb4-7857-4236-baae-83e4a7e4738a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Theorems.Thm_GlobalTheory_UU_SchurComp_proportional_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
namespace GlobalTheory.UU.SchurComp
theorem _root_.solution {F : Type} [CommRing F] (hF : IsField F) {A : Type} [CommGroup A] [Finite A] {E : Type}
    [AddCommGroup E] [Module F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Finite K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Nat.card K * Nat.card H) {n : ℕ} (hn : Nat.card K * n ≤ Module.finrank F E)
    {X Q : Type} [CommRing Q] (ι : F →+* Q) (cl : X → K) (ex : X → E → Q)
    (hex : ∀ β c v v', ex β (c • v + v') = ι c * ex β v + ex β v')
    (hinj : ∀ v, (∀ β, ex β v = 0) → v = 0)
    (hP : ∀ k v, ∃ v', ∀ β, (cl β = k → ex β v' = ex β v) ∧ (cl β ≠ k → ex β v' = 0))
    (hne : ∀ k, ∃ β, cl β = k ∧ ∃ v, ex β v ≠ 0)
    (h3 : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v, (∀ γ, cl γ ≠ cl β → ex γ v = 0) → ex β v = 0 → v = 0)
    (hb : ∀ β, ∃ b : Fin n → Q, ∀ v, ∃ c : Fin n → F, ex β v = ∑ i, ι (c i) * b i)
    (hΦ : ∀ h β v, ex β v = 0 → ex β (Φ (m h) v) = 0)
    (α α' : X) (hα : ∃ v, ex α v ≠ 0) (f₁ : E → Q) (hf₁ : ∀ c v v', f₁ (c • v + v') = ι c * f₁ v + f₁ v')
    (hk : ∀ v, f₁ v = 0 ↔ ex α v = 0)
    (b : Fin n → Q) (hb₁ : ∀ v, ∃ c : Fin n → F, f₁ v = ∑ i, ι (c i) * b i)
    (hb₂ : ∀ v, ∃ c : Fin n → F, ex α' v = ∑ i, ι (c i) * b i)
    (hint : ∀ h v v', ex α' v = f₁ v' → ex α' (Φ (m h) v) = f₁ (Φ (m h) v')) :
    ∃ a : F, ∀ v, ex α' v = ι a * f₁ v := by
  letI := hF.toField
  letI : Algebra F Q := ι.toAlgebra
  have mk : ∀ f : E → Q, (∀ c v v', f (c • v + v') = ι c * f v + f v') → ∃ g : E →ₗ[F] Q, ⇑g = f := fun f hf => by
    have h0 : f 0 = 0 := by
      have := hf 1 0 0
      rw [map_one, one_mul, one_smul, add_zero] at this
      exact left_eq_add.1 this
    exact ⟨⟨⟨f, fun v v' => by have := hf 1 v v'; rwa [map_one, one_mul, one_smul] at this⟩,
      fun c v => by have := hf c v 0; rwa [h0, add_zero, add_zero] at this⟩, rfl⟩
  have sp : ∀ (b : Fin n → Q) (q : Q), (∃ c : Fin n → F, q = ∑ i, ι (c i) * b i) →
      q ∈ Submodule.span F (Set.range b) := fun b q ⟨c, hc⟩ =>
    (Submodule.mem_span_range_iff_exists_fun F).2 ⟨c, hc.symm⟩
  choose ex' hex' using fun β => mk (ex β) (hex β)
  obtain rfl : ex = fun β => ⇑(ex' β) := funext fun β => (hex' β).symm
  obtain ⟨g₁, rfl⟩ := mk f₁ hf₁
  exact proportional_field e Φ hdim hmul hcomm hnd m hm hc hn cl ex' hinj hP hne h3
    (fun β => (hb β).imp fun b hb v => sp b _ (hb v)) hΦ α hα g₁ (ex' α') hk b (fun v => sp b _ (hb₁ v))
    (fun v => sp b _ (hb₂ v)) hint
end GlobalTheory.UU.SchurComp
