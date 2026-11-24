-- Prove2me | solution 1 for GlobalTheory.QuotInt.integral_eq_zero_of_avg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:03.329001+00:00
-- url     : https://prove2.me/submissions/59b1e243-82dc-405b-9dc7-5bbf9ac7cf98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Theorems.Thm_GlobalTheory_QuotInt_sb_right
import Theorems.Thm_GlobalTheory_QuotInt_exists_open_stab
import Theorems.Thm_GlobalTheory_QuotInt_sb_of_quot
import Theorems.Thm_GlobalTheory_QuotInt_finite_quot
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.QuotInt
theorem _root_.solution [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G)) (hKc : IsCompact (K₀ : Set G))
    (R : Subgroup G) (Λ : (G → ℂ) → ℂ)
    (hadd : ∀ φ ∈ SB G, ∀ ψ ∈ SB G, Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℂ) φ, Λ (fun g => a * φ g) = a * Λ φ)
    (hcongr : ∀ φ ψ, (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ)
    (hleft : ∀ r ∈ R, ∀ φ, Λ (fun g => φ (r * g)) = Λ φ)
    (hpos : ∀ φ ∈ SB G, (∀ g, φ g = 0 ∨ φ g = 1) → (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0)
    {F : G → ℂ} (hF : F ∈ SB G) (h0 : ∀ h, Λ (fun g => F (g * h)) = 0) : ∫ g, F g ∂μ = 0 := by
  classical
  obtain ⟨K₁, hK₁, hinv⟩ := exists_open_stab hF
  set K : Subgroup G := K₀ ⊓ K₁ with hK
  have ho : IsOpen (K : Set G) := hKo.inter hK₁
  have hc : IsCompact (K : Set G) := hKc.inter_right (K₁.isClosed_of_isOpen hK₁)
  obtain ⟨S, hS⟩ := finite_quot K ho hF.2
  let ind : G ⧸ K → G → ℂ := fun q g => if (g : G ⧸ K) = q then 1 else 0
  have hind : ∀ q, ind q ∈ SB G := fun q =>
    sb_of_quot K ho hc {q} (fun x => if x = q then 1 else 0) (by intro x hx; simpa using hx)
  have hout : ∀ g : G, F (g : G ⧸ K).out = F g := by
    intro g
    have : g⁻¹ * (g : G ⧸ K).out ∈ K := QuotientGroup.eq.1 (by simp)
    simpa using hinv g _ this.2
  have hdec : ∀ g, F g = ∑ q ∈ S, F q.out * ind q g := by
    intro g
    simp only [ind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with h
    · exact (hout g).symm
    · exact image_eq_zero_of_notMem_tsupport fun hg => h (hS g hg)
  have hz : Λ (fun _ => 0) = 0 := by simpa using hsmul 0 0
  have hsum : ∀ (T : Finset (G ⧸ K)) (h : G), Λ (fun g => ∑ q ∈ T, F q.out * ind q (g * h)) =
      ∑ q ∈ T, F q.out * Λ (fun g => ind q (g * h)) := by
    intro T h
    induction T using Finset.induction_on with
    | empty => simpa using hz
    | insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      rw [← ih, ← hsmul, ← hadd]
      · rfl
      · exact (SB G).smul_mem (F a.out) (sb_right (hind a) h)
      · have := (SB G).sum_mem (t := T) fun q _ => (SB G).smul_mem (F q.out) (sb_right (hind q) h)
        convert this using 1
        ext g; simp
  have hshift : ∀ (r : G) (q : G ⧸ K) (g : G), ind (r • q) g = ind q (r⁻¹ * g) := by
    intro r q g
    have : ((r⁻¹ * g : G) : G ⧸ K) = r⁻¹ • (g : G ⧸ K) := rfl
    simp only [ind, this, inv_smul_eq_iff]
  have htot : ∑ q ∈ S, F q.out = 0 := by
    apply Finset.sum_cancels_of_partition_cancels (MulAction.orbitRel R (G ⧸ K))
    intro x _
    have hc0 : Λ (fun g => ind x (g * x.out)) ≠ 0 := by
      refine hpos _ (sb_right (hind x) _) (fun g => ?_) ⟨1, R.one_mem, by simp [ind]⟩
      simp only [ind]; split_ifs <;> simp
    have := h0 x.out
    simp only [hdec (_ * x.out)] at this
    rw [hsum] at this
    apply mul_right_cancel₀ hc0
    rw [zero_mul, ← this, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · obtain ⟨r, rfl⟩ := hq
      congr 1
      rw [← hleft r⁻¹ (R.inv_mem r.2)]
      congr 1; ext g
      change _ = ind ((r : G) • x) _
      rw [hshift, mul_assoc]
    · rw [hcongr (fun g => ind q (g * x.out)) (fun _ => 0), hz, mul_zero]
      intro r hr
      simp only [ind, ite_eq_right_iff]
      intro h
      refine absurd ⟨⟨r, hr⟩, ?_⟩ hq
      rw [← h]
      change r • x = r • ((x.out : G) : G ⧸ K)
      simp
  have hint : ∀ q, ∫ g, ind q g ∂μ = ∫ g, ind ((1 : G) : G ⧸ K) g ∂μ := by
    intro q
    have : q = q.out • ((1 : G) : G ⧸ K) := by
      change q = ((q.out * 1 : G) : G ⧸ K)
      simp
    rw [this]
    simp only [hshift]
    exact integral_mul_left_eq_self _ _
  rw [show (fun g => F g) = fun g => ∑ q ∈ S, F q.out * ind q g from funext hdec, integral_finset_sum]
  · simp only [integral_const_mul, hint]
    rw [← Finset.sum_mul, htot, zero_mul]
  · intro q _
    exact ((hind q).1.continuous.integrable_of_hasCompactSupport (hind q).2).const_mul _
end GlobalTheory.QuotInt
