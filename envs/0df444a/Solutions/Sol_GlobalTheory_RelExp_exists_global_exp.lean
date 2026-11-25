-- Prove2me | solution 1 for GlobalTheory.RelExp.exists_global_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:34:44.562181+00:00
-- url     : https://prove2.me/submissions/2f1aaed8-a5c7-4ad6-946a-98774b05dbca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually_near
import Theorems.Thm_GlobalTheory_RelExp_exists_local_exp
import Theorems.Thm_GlobalTheory_RelExp_HolAt_comp
import Theorems.Thm_GlobalTheory_RelExp_HolAt_congr
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually
import Theorems.Thm_GlobalTheory_RelExp_HolAt_one
import Theorems.Thm_GlobalTheory_RelExp_HolAt_pow
import Theorems.Thm_GlobalTheory_RelExp_exists_addMonoidHom_eqOn_ball


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
    {B : Set (Fin m → ℂ)} (hB : B ∈ 𝓝 b₀)
    (hy : HolAt y b₀) (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U)
    (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O) {s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hs1 : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0))
    (hs2 : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2)
    (hs3 : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a) :
    ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ)
      (Q : Set ((Fin m → ℂ) × (Fin g → ℂ))) (L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ 0 < r ∧ IsOpen Q ∧ (∀ b z w, e b (z + w) = e b z * e b w) ∧
      (∀ b ∈ B', (∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (b, z)) ∧
        ⊤ ≤ pt (1 : Over.mk (y b) ⟶ G) ⁻¹ᵁ U ∧ (b, crd U f (pt (1 : Over.mk (y b) ⟶ G))) ∈ O ∧ (b, 0) ∈ Q ∧
        HasFDerivAt (fun z => crd U t (pt (e b z))) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
        L (b, 0) = 0 ∧ AnalyticAt ℂ L (b, 0) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧
      ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → (b, crd0 t a) ∈ Q →
        e b (L (b, crd0 t a)) = a := by
  obtain ⟨E, L, hE, hL, h0, hLE, hadd⟩ := exists_local_exp hexp hy hOo hU hO hs1 hs2 hs3
  have hE0 : E (b₀, 0) = 0 := h0.self_of_nhds.1
  have hL0 : L (b₀, 0) = 0 := by
    have := hLE.self_of_nhds.1
    rwa [hE0] at this
  have hτ : AnalyticAt ℂ (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, E q)) (b₀, 0) := analyticAt_fst.prod hE
  have hψ : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 (E q))) (b₀, 0) := by
    have := HolAt.comp (a := fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2))
      (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, E q)) (v₀ := (b₀, 0)) (by simpa only [hE0] using hs1) hτ
    exact this
  have hcE : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 (E q)) = E q := by
    have := hτ.continuousAt.tendsto
    simp only [hE0] at this
    exact this.eventually hs2

  obtain ⟨r₁, hr₁, h₁⟩ := Metric.eventually_nhds_iff_ball.1 (hψ.eventually.and (hcE.and hLE))
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff_ball.1 hadd
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  set r := min r₁ r₂ with hrdef
  have k₁ : ∀ b ∈ Metric.ball b₀ r, ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, _ := fun b hb v hv =>
    h₁ (b, v) (Metric.ball_subset_ball (min_le_left _ _) (by rw [← ball_prod_same]; exact ⟨hb, hv⟩))
  have hex : ∀ b, ∃ ε : (Fin g → ℂ) →+ Additive (Over.mk (y b) ⟶ G), b ∈ Metric.ball b₀ r →
      ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, (ε v).toMul = s b (E (b, v)) := by
    intro b
    by_cases hb : b ∈ Metric.ball b₀ r
    · obtain ⟨ε, hε⟩ := exists_addMonoidHom_eqOn_ball (g := fun v => Additive.ofMul (s b (E (b, v)))) hr
        fun v hv v' hv' => congrArg Additive.ofMul (h₂ (b, v, v') (Metric.ball_subset_ball (min_le_right _ _)
          (by rw [← ball_prod_same, ← ball_prod_same]; exact ⟨hb, hv, hv'⟩)))
      exact ⟨ε, fun _ v hv => congrArg Additive.toMul (hε v hv)⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose ε hε using hex
  obtain ⟨Q, hQ, hQo, hQ0⟩ := eventually_nhds_iff.1 (hL.eventually_analyticAt.and (hLE.and
    (((continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually (Metric.ball_mem_nhds b₀ hr)).and
      (hL.continuousAt.eventually (by rw [hL0]; exact Metric.ball_mem_nhds 0 hr)))))
  have hQb : ∀ᶠ b in 𝓝 b₀, (b, (0 : Fin g → ℂ)) ∈ Q :=
    (Continuous.tendsto (f := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (by fun_prop) b₀).eventually
      (hQo.mem_nhds hQ0)
  obtain ⟨B', hB', hB'o, hB'0⟩ := eventually_nhds_iff.1 (Filter.Eventually.and hB (h0.and (hQb.and
    (HolAt.eventually_near (β := fun b => b) (a := fun _ => 1) (HolAt.one hy) continuousAt_id rfl hOo hU hO))))
  refine ⟨B', fun b v => (ε b v).toMul, r, Q, L, hB'o, hB'0, fun b hb => (hB' b hb).1, hr, hQo,
    fun b z w => congrArg Additive.toMul ((ε b).map_add z w), fun b hb => ?_, fun b a ha hf hq => ?_⟩
  · obtain ⟨-, ⟨hEb, hEd⟩, hbQ, hbU, hbO⟩ := hB' b hb
    have hbr : b ∈ Metric.ball b₀ r := (hQ _ hbQ).2.2.1
    have hLb : L (b, 0) = 0 := by
      have := (hQ _ hbQ).2.1.1
      rwa [hEb] at this
    refine ⟨fun z => ?_, hbU, hbO, hbQ, ?_, hLb, (hQ _ hbQ).1, fun z hz h1 => ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_gt (‖z‖ / r)
      have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
      have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
      have hz : (k : ℂ)⁻¹ • z ∈ Metric.ball (0 : Fin g → ℂ) r := by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_lt_iff₀ hk0]
        rwa [div_lt_iff₀ hr] at hk
      have hφ : AnalyticAt ℂ (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, (k : ℂ)⁻¹ • q.2)) (b, z) :=
        analyticAt_fst.prod (analyticAt_snd.const_smul (c := (k : ℂ)⁻¹))
      have h0' := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, (k : ℂ)⁻¹ • q.2)) (v₀ := (b, z))
        (k₁ b hbr _ hz).1 hφ
      have h1 := (HolAt.pow (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) => y q.1)
        (a := fun q => s q.1 (E (q.1, (k : ℂ)⁻¹ • q.2))) h0' k)
      refine h1.congr ?_
      filter_upwards [hφ.continuousAt.eventually (prod_mem_nhds (Metric.isOpen_ball.mem_nhds hbr)
        (Metric.isOpen_ball.mem_nhds hz))] with q hq
      rw [← hε q.1 hq.1 _ hq.2, ← toMul_nsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hkc]
    · refine (hEd.add_const (crd U t (pt (1 : Over.mk (y b) ⟶ G)))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Fin g → ℂ) hr] with v hv
      rw [hε b hbr v hv]
      exact sub_eq_iff_eq_add.1 (k₁ b hbr v hv).2.1
    · have hz' := mem_ball_zero_iff.2 hz
      have h2 := (k₁ b hbr z hz').2
      have h3 : s b (E (b, z)) = 1 := (hε b hbr z hz').symm.trans h1
      have h4 : E (b, z) = 0 := by
        rw [← h2.1]
        simp only [h3, crd0, sub_self]
      have h5 := h2.2.1
      simp only [h4, hLb] at h5
      exact h5.symm
  · obtain ⟨-, h1, h2, h3⟩ := hQ _ hq
    refine (hε b h2 _ h3).trans ?_
    rw [h1.2]
    exact hs3 b a ha hf
end GlobalTheory.RelExp
