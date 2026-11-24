-- Prove2me | solution 1 for GlobalTheory.SS.Dil.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:35.918696+00:00
-- url     : https://prove2.me/submissions/29a9627f-e2ab-4fdd-b82a-16923b1767c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Theorems.Thm_GlobalTheory_SS_Dil_span_d
import Theorems.Thm_GlobalTheory_SS_Dil_dd_add
import Theorems.Thm_GlobalTheory_SS_Dil_dd_mul
import Theorems.Thm_GlobalTheory_SS_Dil_dd_algebraMap
import Theorems.Thm_GlobalTheory_SS_Dil_dd_zero
import Theorems.Thm_GlobalTheory_SS_Dil_chain
import Theorems.Thm_GlobalTheory_SS_Dil_gr_add
import Theorems.Thm_GlobalTheory_SS_Dil_gr_sub
import Theorems.Thm_GlobalTheory_SS_Dil_gr_mul
import Theorems.Thm_GlobalTheory_SS_Dil_gr_C
import Theorems.Thm_GlobalTheory_SS_Dil_gr_sum
import Theorems.Thm_GlobalTheory_SS_Dil_ker_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R B B' S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra B S] [Algebra B' S] (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q)
    (σ : MvPolynomial (Fin n) R →+* S) (hσ : ∀ p, σ p = algebraMap B S (q p))
    (φ : B →ₐ[R] B') (hφ : ∀ b, algebraMap B' S (φ b) = algebraMap B S b) (π : R) (ϖ : S)
    (hϖ : algebraMap B' S (algebraMap R B' π) = ϖ) (hreg : ∀ x, ϖ * x = 0 → x = 0)
    (hreg' : ∀ x, algebraMap R B' π * x = 0 → x = 0) (I : Ideal (MvPolynomial (Fin n) R))
    (hβ : ∀ g ∈ I, ∃ b', algebraMap R B' π * b' = φ (q g)) (hJ : ∀ f, q f = 0 → f ∈ I)
    (hgen : ∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ (q g) → Q b') →
      (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x)
    (h : Fin n → MvPolynomial (Fin n) R) (hh : ∀ j, h j ∈ I)
    (hA : ∀ g ∈ I, ∃ p, g - ∑ j, pderiv j g * h j - MvPolynomial.C π * p ∈ I * I)
    (h' : Fin n → MvPolynomial (Fin n) R) (hh' : ∀ j, q (h' j) = 0)
    (hB : ∀ f, q f = 0 → f - ∑ j, pderiv j f * h' j ∈ I * I)
    (m : S ⊗[B'] KaehlerDifferential R B') :
    ∃ u : Fin n → S, ϖ • m = ∑ i, u i • dd R B' S (φ (q (X i))) ∧
      ∀ c : ℕ, ϖ ^ (c + 1) • ∑ i, u i • dd R B S (q (X i)) = 0 → ϖ ^ c • m = 0 := by
  have hσ' : ∀ p, σ p = algebraMap B' S (φ (q p)) := fun p => by rw [hφ, hσ]
  have hregF : ∀ u : Fin n → S, ϖ • u = 0 → u = 0 := fun u hu => funext fun i => hreg _ (congrFun hu i)
  have huniq : ∀ x y, algebraMap R B' π * x = algebraMap R B' π * y → x = y := fun x y e =>
    sub_eq_zero.1 (hreg' _ (by rw [mul_sub, e, sub_self]))
  have hCπ : φ (q (C π)) = algebraMap R B' π := by rw [← algebraMap_eq, q.commutes, φ.commutes]
  let ψ : (Fin n → S) →ₗ[S] S ⊗[B'] KaehlerDifferential R B' :=
    Fintype.linearCombination S (fun i => dd R B' S (φ (q (X i))))
  have hψ : ∀ u, ψ u = ∑ i, u i • dd R B' S (φ (q (X i))) := fun u => Fintype.linearCombination_apply _ _ _
  have hψg : ∀ p, ψ (gr σ p) = dd R B' S (φ (q p)) := fun p => by
    rw [hψ]
    exact (chain σ (fun p => dd R B' S (φ (q p))) (fun x y => by rw [map_add, map_add, dd_add])
      (fun x y => by rw [map_mul, map_mul, dd_mul, hσ', hσ'])
      (fun r => by rw [← algebraMap_eq, q.commutes, φ.commutes, dd_algebraMap]) p).symm
  let j : (Fin n → S) →ₗ[S] (Fin n → S) × (S ⊗[B'] KaehlerDifferential R B') := LinearMap.prod (ϖ • LinearMap.id) ψ
  have hj : ∀ u, j u = (ϖ • u, ψ u) := fun u => rfl
  have hval : ∀ g b', algebraMap R B' π * b' = φ (q g) → σ g = ϖ * algebraMap B' S b' := fun g b' e => by
    rw [hσ', ← e, map_mul, hϖ]
  have hdd : ∀ g b', algebraMap R B' π * b' = φ (q g) → ϖ • dd R B' S b' = ψ (gr σ g) := fun g b' e => by
    rw [hψg, ← e, dd_mul, dd_algebraMap, smul_zero, add_zero, hϖ]
  choose β hβh using fun i => hβ (h i) (hh i)
  let θ : (Fin n → S) →ₗ[S] (Fin n → S) × (S ⊗[B'] KaehlerDifferential R B') :=
    Fintype.linearCombination S (fun i => (gr σ (h i), dd R B' S (β i)))
  have hθ : ∀ u, θ u = ∑ i, u i • (gr σ (h i), dd R B' S (β i)) := fun u => Fintype.linearCombination_apply _ _ _
  have hθϖ : ∀ u, ϖ • θ u ∈ LinearMap.range j := fun u => by
    rw [hθ, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_comm]
    refine Submodule.smul_mem _ _ ⟨gr σ (h i), ?_⟩
    rw [hj, Prod.smul_mk, hdd _ _ (hβh i)]
  let W : Submodule S ((Fin n → S) × (S ⊗[B'] KaehlerDifferential R B')) :=
    (LinearMap.range j).comap (LinearMap.id - θ ∘ₗ LinearMap.fst S _ _)
  have hW : ∀ w, w ∈ W ↔ w - θ w.1 ∈ LinearMap.range j := fun w => Iff.rfl
  have hjW : ∀ w ∈ LinearMap.range j, w ∈ W := by
    rintro _ ⟨u, rfl⟩
    rw [hW]
    refine Submodule.sub_mem _ ⟨u, rfl⟩ ?_
    rw [hj, map_smul]; exact hθϖ u
  have key : ∀ x, ((0 : Fin n → S), x) ∈ W → x = 0 := by
    intro x hx
    rw [hW, map_zero, sub_zero] at hx
    obtain ⟨u, hu⟩ := hx
    rw [hj, Prod.mk.injEq] at hu
    rw [← hu.2, hregF u hu.1, map_zero]
  have S1 : ∀ e ∈ I * I, ∃ b', algebraMap R B' π * b' = φ (q e) ∧ (gr σ e, dd R B' S b') ∈ LinearMap.range j := by
    intro e he
    refine Submodule.mul_induction_on he ?_ ?_
    · intro g hg g' hg'
      obtain ⟨b, hb⟩ := hβ g hg
      obtain ⟨b', hb'⟩ := hβ g' hg'
      refine ⟨φ (q g) * b', by rw [map_mul, map_mul, ← hb']; ring,
        algebraMap B' S b • gr σ g' + algebraMap B' S b' • gr σ g, ?_⟩
      rw [hj, gr_mul, dd_mul, ← hσ', hval g b hb, hval g' b' hb', map_add, map_smul, map_smul, ← hdd g' b' hb', hψg]
      congr 1
      · rw [smul_add, mul_smul, mul_smul]
      · rw [mul_comm, mul_smul]
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', by rw [mul_add, hb, hb', map_add, map_add], ?_⟩
      rw [gr_add, dd_add]
      exact Submodule.add_mem _ hx hy
  have hΔ : ∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ (q g) → (gr σ g, dd R B' S b') ∈ W := by
    intro g hg b' hb'
    obtain ⟨p, hp⟩ := hA g hg
    obtain ⟨e, he, he'⟩ := S1 _ hp
    have e1 : b' = e + ∑ i, φ (q (pderiv i g)) * β i + φ (q p) := by
      apply huniq
      rw [mul_add, mul_add, he, hb', Finset.mul_sum]
      simp only [map_sub, map_sum, map_mul, hCπ, ← hβh]
      simp only [mul_left_comm (algebraMap R B' π)]
      ring
    have ddsum : ∀ f : Fin n → B', dd R B' S (∑ i, f i) = ∑ i, dd R B' S (f i) := fun f => by
      simp [dd, tmul_sum]
    have e2 : (gr σ g, dd R B' S b') - θ (gr σ g) =
        (gr σ (g - ∑ j, pderiv j g * h j - MvPolynomial.C π * p), dd R B' S e) + j (gr σ p) +
          ∑ i, algebraMap B' S (β i) • j (gr σ (pderiv i g)) := by
      rw [hθ]
      ext1
      · simp only [Prod.fst_sub, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, hj, gr_sub, gr_sum, gr_mul, gr_C,
          hσ' (C π), hCπ, hϖ, smul_zero, add_zero, Finset.sum_add_distrib, fun i => hval _ _ (hβh i), smul_smul,
          mul_comm ϖ]
        have : ∀ i, gr σ g i = σ (pderiv i g) := fun _ => rfl
        simp only [this]
        abel
      · simp only [Prod.snd_sub, Prod.snd_add, Prod.snd_sum, Prod.smul_snd, hj, hψg]
        rw [e1, dd_add, dd_add, ddsum]
        have : ∀ i, gr σ g i = σ (pderiv i g) := fun _ => rfl
        simp only [this, dd_mul, ← hσ', Finset.sum_add_distrib]
        abel
    rw [hW]
    show (gr σ g, dd R B' S b') - θ (gr σ g) ∈ _
    rw [e2]
    exact Submodule.add_mem _ (Submodule.add_mem _ he' ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ⟨_, rfl⟩)
  have S2 : ∀ e ∈ I * I, ∃ b', algebraMap R B' π * (algebraMap R B' π * b') = φ (q e) ∧
      ∃ u, ϖ • u = gr σ e ∧ (u, dd R B' S b') ∈ W := by
    intro e he
    refine Submodule.mul_induction_on he ?_ ?_
    · intro g hg g' hg'
      obtain ⟨b, hb⟩ := hβ g hg
      obtain ⟨b', hb'⟩ := hβ g' hg'
      refine ⟨b * b', by rw [map_mul, map_mul, ← hb', ← hb]; ring,
        algebraMap B' S b • gr σ g' + algebraMap B' S b' • gr σ g, ?_, ?_⟩
      · rw [gr_mul, hval g b hb, hval g' b' hb', smul_add, mul_smul, mul_smul]
      · rw [dd_mul]
        exact W.add_mem (W.smul_mem _ (hΔ g' hg' b' hb')) (W.smul_mem _ (hΔ g hg b hb))
    · rintro x y ⟨b, hb, u, hu, hx⟩ ⟨b', hb', u', hu', hy⟩
      refine ⟨b + b', by rw [mul_add, mul_add, hb, hb', map_add, map_add], u + u', by rw [smul_add, hu, hu', gr_add], ?_⟩
      rw [dd_add]
      exact W.add_mem hx hy
  let θ' : (Fin n → S) →ₗ[S] (Fin n → S) := Fintype.linearCombination S (fun i => gr σ (h' i))
  have hθ' : ∀ u, θ' u = ∑ i, u i • gr σ (h' i) := fun u => Fintype.linearCombination_apply _ _ _
  let W₁ : Submodule S (Fin n → S) := W.comap (LinearMap.inl S _ _)
  have hW₁ : ∀ u, u ∈ W₁ ↔ (u, (0 : S ⊗[B'] KaehlerDifferential R B')) ∈ W := fun _ => Iff.rfl
  have hθ'W : ∀ u, θ' u ∈ W₁ := fun u => by
    rw [hθ']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have := hΔ (h' i) (hJ _ (hh' i)) 0 (by rw [hh', map_zero, mul_zero])
    rwa [dd_zero] at this
  let N : Submodule S (Fin n → S) := (W₁.map (ϖ • LinearMap.id)).comap (LinearMap.id - θ')
  have hN : ∀ v, v ∈ N ↔ ∃ u ∈ W₁, ϖ • u = v - θ' v := fun _ => Iff.rfl
  have hNJ : ∀ f, q f = 0 → gr σ f ∈ N := by
    intro f hf
    obtain ⟨b, hb, u, hu, hw⟩ := S2 _ (hB f hf)
    have hb0 : b = 0 := hreg' _ (hreg' _ (by rw [hb]; simp [hf, hh']))
    rw [hb0, dd_zero] at hw
    refine (hN _).2 ⟨u, hw, ?_⟩
    rw [hu, gr_sub, gr_sum, hθ']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gr_mul, hσ (h' i), hh', map_zero, zero_smul, add_zero]; rfl
  have hsur : m ∈ W.map (LinearMap.snd S _ _) := by
    refine span_d R B' S _ (fun b => ?_) m
    show dd R B' S b ∈ _
    refine hgen (fun b => dd R B' S b ∈ W.map (LinearMap.snd S _ _)) ?_ ?_ ?_ ?_ b
    · intro b
      obtain ⟨p, rfl⟩ := hq b
      exact ⟨j (gr σ p), hjW _ ⟨_, rfl⟩, hψg p⟩
    · intro g hg b' hb'
      exact ⟨_, hΔ g hg b' hb', rfl⟩
    · intro x y hx hy
      show dd R B' S (x + y) ∈ _
      rw [dd_add]; exact Submodule.add_mem _ hx hy
    · intro x y hx hy
      show dd R B' S (x * y) ∈ _
      rw [dd_mul]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)
  obtain ⟨⟨u, m⟩, hw, rfl⟩ := hsur
  show ∃ u : Fin n → S, ϖ • m = ∑ i, u i • dd R B' S (φ (q (X i))) ∧
      ∀ c : ℕ, ϖ ^ (c + 1) • ∑ i, u i • dd R B S (q (X i)) = 0 → ϖ ^ c • m = 0
  refine ⟨u, ?_, fun c hc => ?_⟩
  · have h1 : ϖ • (u, m) ∈ LinearMap.range j := by
      have := Submodule.add_mem _ (Submodule.smul_mem _ ϖ ((hW _).1 hw)) (hθϖ u)
      rwa [← smul_add, sub_add_cancel] at this
    obtain ⟨v, hv⟩ := h1
    rw [hj, Prod.smul_mk, Prod.mk.injEq] at hv
    have : v = u := sub_eq_zero.1 (hregF _ (by rw [smul_sub, hv.1, sub_self]))
    rw [← hv.2, this, hψ]
  · have h1 : ϖ • ϖ ^ c • u ∈ N := ker_le q hq σ hσ N hNJ _ (by
      rw [← hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, pow_succ']; rfl)
    obtain ⟨v, hv, e⟩ := (hN _).1 h1
    have e' : ϖ ^ c • u = v + θ' (ϖ ^ c • u) := sub_eq_zero.1 (hregF _ (by
      rw [smul_sub, smul_add, e, map_smul θ' ϖ]; abel))
    have h2 : ϖ ^ c • u ∈ W₁ := by rw [e']; exact W₁.add_mem hv (hθ'W _)
    apply key
    have := W.sub_mem (W.smul_mem (ϖ ^ c) hw) ((hW₁ _).1 h2)
    simpa using this
end GlobalTheory.SS.Dil
