-- Prove2me | solution 1 for GlobalTheory.RelExp.exists_centred_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:25.96467+00:00
-- url     : https://prove2.me/submissions/59f4607a-2467-4a1f-a2e3-76d8066a3b7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
import Theorems.Thm_GlobalTheory_RelExp_HolAt_analyticAt_pi
import Theorems.Thm_GlobalTheory_RelExp_HolAt_comp
import Theorems.Thm_GlobalTheory_RelExp_HolAt_congr
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually
import Theorems.Thm_GlobalTheory_RelExp_HolAt_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {X : Scheme.{0}} {G : Over X}
variable [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} {U : G.left.Opens}
  {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
namespace GlobalTheory.RelExp
theorem _root_.solution (hy : HolAt y b₀) {N : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} (hN : IsOpen N)
    (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U) (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O)
    (hσ : IsHolTo N σ) (hσN : ∀ q ∈ N, σ q ≫ G.hom = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i)
    (hinv : ∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ G.left), x ≫ G.hom = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, crd U f x) ∈ O →
      (b, crd U t x) ∈ N ∧ σ (b, crd U t x) = x) :
    ∃ s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G),
      HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2) ∧
      ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a := by
  classical
  let c : (Fin m → ℂ) → (Fin g → ℂ) := fun b => crd U t (pt (1 : Over.mk (y b) ⟶ G))
  have hc : AnalyticAt ℂ c b₀ := (HolAt.one (G := G) hy).analyticAt_pi hU t
  let τ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) := fun q => (q.1, q.2 + c q.1)
  have hτ : AnalyticAt ℂ τ (b₀, 0) :=
    analyticAt_fst.prod (analyticAt_snd.add (AnalyticAt.comp (g := c) hc analyticAt_fst))
  have hτ0 : τ (b₀, 0) ∈ N := by
    have := (hinv b₀ _ (Over.w (1 : Over.mk (y b₀) ⟶ G)) hU hO).1
    simpa only [τ, zero_add] using this
  let s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G) := fun b w =>
    if h : τ (b, w) ∈ N then Over.homMk (σ (τ (b, w))) (hσN _ h).1 else 1
  have hs : ∀ q, τ q ∈ N → pt (s q.1 q.2) = σ (τ q) := fun q hq => by
    have : s q.1 q.2 = Over.homMk (σ (τ q)) (hσN _ hq).1 := dif_pos hq
    rw [this]; rfl
  have hev : ∀ᶠ q in 𝓝 (b₀, (0 : Fin g → ℂ)), τ q ∈ N := hτ.continuousAt.eventually (hN.mem_nhds hτ0)
  refine ⟨s, (HolAt.comp ⟨N, hN, hτ0, hσ⟩ hτ).congr (hev.mono fun q hq => (hs q hq).symm), hev.mono fun q hq => ?_,
    fun b a ha hf => ?_⟩
  · have : crd U t (pt (s q.1 q.2)) = q.2 + c q.1 := by
      rw [hs q hq]; exact funext (hσN _ hq).2.2
    exact sub_eq_iff_eq_add.2 this
  · obtain ⟨h1, h2⟩ := hinv b _ (Over.w a) ha hf
    have e : τ (b, crd0 t a) = (b, crd U t (pt a)) := Prod.ext rfl (sub_add_cancel _ _)
    refine Over.OverMorphism.ext ((hs (b, crd0 t a) (e ▸ h1)).trans ?_)
    rw [e]; exact h2
end GlobalTheory.RelExp
