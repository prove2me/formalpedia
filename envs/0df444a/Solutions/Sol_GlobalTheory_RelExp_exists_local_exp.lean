-- Prove2me | solution 1 for GlobalTheory.RelExp.exists_local_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:05.732295+00:00
-- url     : https://prove2.me/submissions/214fdb31-f444-473e-be23-8f86b115d2e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
import Theorems.Thm_GlobalTheory_RelExp_HolAt_analyticAt_coordinate_zero
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually_near
import Theorems.Thm_GlobalTheory_RelExp_HolAt_comp
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually
import Theorems.Thm_GlobalTheory_RelExp_HolAt_mul
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
theorem _root_.solution [IsCommMonObj G]
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hy : HolAt y b₀) (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U)
    (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O) {s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hs1 : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0))
    (hs2 : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2)
    (hs3 : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a) :
    ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧
      (∀ᶠ b in 𝓝 b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧
      ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
        s q.1 (E (q.1, q.2.1 + q.2.2)) = s q.1 (E (q.1, q.2.1)) * s q.1 (E (q.1, q.2.2)) := by
  have hs0 : ∀ᶠ b in 𝓝 b₀, s b 0 = 1 := by
    filter_upwards [HolAt.eventually_near (β := fun b => b) (a := fun _ => 1) (HolAt.one hy) continuousAt_id rfl
      hOo hU hO] with b hb
    simpa only [crd0, sub_self] using hs3 b 1 hb.1 hb.2
  have hprod : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2.1 * s q.1 q.2.2))
      (b₀, 0, 0) := by
    have k1 := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.1)) (v₀ := (b₀, 0, 0))
      hs1 (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
    have k2 := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.2)) (v₀ := (b₀, 0, 0))
      hs1 (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd))
    exact HolAt.mul (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => y q.1)
      (a := fun q => s q.1 q.2.1) (b := fun q => s q.1 q.2.2) k1 k2
  have h11 : s b₀ 0 * s b₀ 0 = 1 := by rw [hs0.self_of_nhds, _root_.mul_one]
  let M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun q => crd0 t (s q.1 q.2.1 * s q.1 q.2.2)
  have hMa : AnalyticAt ℂ M (b₀, 0, 0) :=
    HolAt.analyticAt_coordinate_zero (β := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => q.1)
      (a := fun q => s q.1 q.2.1 * s q.1 q.2.2) hprod h11 hU
  have hM : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
      s q.1 (M q) = s q.1 q.2.1 * s q.1 q.2.2 :=
    (HolAt.eventually_near (β := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => q.1)
      (a := fun q => s q.1 q.2.1 * s q.1 q.2.2) hprod
      continuousAt_fst h11 hOo hU hO).mono fun q hq => hs3 _ _ hq.1 hq.2
  obtain ⟨E, L, hE, hL, h0, hLE, hadd⟩ := hexp m g b₀ M hMa (by
      filter_upwards [hs2, (continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually hs0] with q h1 h2
      show crd0 t (s q.1 q.2 * s q.1 0) = q.2
      rw [h2, _root_.mul_one, h1])
    (Eventually.of_forall fun q => by simp only [M, mul_comm]) (by
      have t1 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        (q.1, q.2.1, q.2.2.1)) (by fun_prop) (b₀, 0, 0, 0)
      have t2 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        (q.1, q.2.2.1, q.2.2.2)) (by fun_prop) (b₀, 0, 0, 0)
      filter_upwards [t1.eventually hM, t2.eventually hM] with q h1 h2
      show crd0 t (s q.1 (M _) * s q.1 q.2.2.2) = crd0 t (s q.1 q.2.1 * s q.1 (M _))
      rw [h1, h2, _root_.mul_assoc])
  refine ⟨E, L, hE, hL, h0, hLE, ?_⟩
  have hEt : Tendsto E (𝓝 (b₀, 0)) (𝓝 0) := by
    have := hE.continuousAt.tendsto
    rwa [h0.self_of_nhds.1] at this
  have t1 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.1))
    (by fun_prop) (b₀, 0, 0)
  have t2 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.2))
    (by fun_prop) (b₀, 0, 0)
  have t3 := ((continuous_fst.tendsto (b₀, (0 : Fin g → ℂ), (0 : Fin g → ℂ))).prodMk_nhds
    ((hEt.comp t1).prodMk_nhds (hEt.comp t2)))
  filter_upwards [hadd, t3.eventually hM] with q h1 h2
  rw [h1]
  exact h2
end GlobalTheory.RelExp
