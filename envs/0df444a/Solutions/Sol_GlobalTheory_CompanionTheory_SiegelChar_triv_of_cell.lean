-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelChar.triv_of_cell
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:11.328293+00:00
-- url     : https://prove2.me/submissions/67dd4767-5f44-4b8d-9490-0a82ab9717f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit_matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar
namespace GlobalTheory.CompanionTheory.SiegelChar
theorem _root_.solution {F : Type} [Field F] [Infinite F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    {β : Type} [Fintype β] [DecidableEq β] {c : E →ₐ[F] E} {ξ : E} (hξ : IsUnit ξ) (h2 : IsUnit (2 : E))
    (hc : c ξ = -ξ) {σ : Matrix β β E →+ Matrix β β E} {G : Type} [Group G] {φ : G →* Matrix β β E}
    {e f : Matrix β β E} (hsm : ∀ (a : E) x, σ (a • x) = c a • σ x) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1)
    (hu : ∀ g, σ (φ g) * φ g = 1) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0) (lam : G →* ℂˣ)
    (hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1) (g : G) : lam g = 1 := by
  classical
  have hinvmat : ∀ A B : Matrix β β E, A * B = 1 → B * A = 1 := fun A B h => mul_eq_one_comm.mp h
  have hunit_of : ∀ A B : Matrix β β E, A * B = 1 → IsUnit A :=
    fun A B h => ⟨⟨A, B, h, hinvmat A B h⟩, rfl⟩
  have hsmul_unit : ∀ (a : E) (A : Matrix β β E), IsUnit a → IsUnit A → IsUnit (a • A) := by
    intro a A ha hA
    rw [Algebra.smul_def]
    exact (ha.map (algebraMap E (Matrix β β E))).mul hA
  have htwo : ∀ A : Matrix β β E, IsUnit A → IsUnit (A + A) := by
    intro A hA
    rw [← two_smul E A]
    exact hsmul_unit 2 A h2 hA
  have fin1 : ∀ (A B : Matrix β β E) (τ : E), IsUnit (A + τ • B) →
      {t : F | ¬ IsUnit (A + algebraMap F E t • B)}.Finite := by
    intro A B τ h
    have h' : IsUnit (A + τ • B + (τ * τ) • (0 : Matrix β β E)) := by rwa [smul_zero, add_zero]
    have hfin := finite_nonunit_matrix (F := F) A B 0 τ h'
    simpa only [smul_zero, add_zero] using hfin
  have finE : ∀ (a b : E) (τ : E), IsUnit (a + b * τ) →
      {t : F | ¬ IsUnit (a + b * algebraMap F E t)}.Finite := by
    intro a b τ h
    have hfin := finite_nonunit (F := F) (Polynomial.C a + Polynomial.C b * Polynomial.X) τ (by simpa using h)
    simpa using hfin
  have hcF : ∀ t : F, c (algebraMap F E t) = algebraMap F E t := fun t => c.commutes t
  have hσF : ∀ (t : F) (y : Matrix β β E), σ (algebraMap F E t • y) = algebraMap F E t • σ y :=
    fun t y => by rw [hsm, hcF]
  have main : ∀ g : G, IsUnit (φ g + 1) → lam g = 1 := by
    intro g hg1
    obtain ⟨x, hx⟩ : ∃ x, x = φ g := ⟨_, rfl⟩
    rw [← hx] at hg1
    have hσx : σ x * x = 1 := by rw [hx]; exact hu g
    have hxσ : x * σ x = 1 := hinvmat _ _ hσx
    have hxu : IsUnit x := hunit_of _ _ hxσ
    have hN := fin1 (x + 1) (x - 1) 0 (by rwa [zero_smul, add_zero])
    have hD := fin1 (x + 1) (-(x - 1)) 0 (by rwa [zero_smul, add_zero])
    have hI := fin1 (x + 1) ((x - 1) * (e - f)) 0 (by rwa [zero_smul, add_zero])
    have hII := fin1 ((x + 1) * (x * e + f)) ((x - 1) * (f - x * e)) 1 (by
      rw [one_smul]
      have h0 : (x + 1) * (x * e + f) + (x - 1) * (f - x * e) = x * (e + f) + x * (e + f) := by
        noncomm_ring
      rw [h0, hef, mul_one]
      exact htwo x hxu)
    obtain ⟨s, hs⟩ := ((hN.union hD).union (hI.union hII)).infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hs
    obtain ⟨⟨hNs, hDs⟩, hIs, hIIs⟩ := hs
    obtain ⟨N, hNdef⟩ : ∃ N : Matrix β β E, N = (x + 1) + algebraMap F E s • (x - 1) := ⟨_, rfl⟩
    obtain ⟨D, hDdef⟩ : ∃ D : Matrix β β E, D = (x + 1) + algebraMap F E s • (-(x - 1)) := ⟨_, rfl⟩
    rw [← hNdef] at hNs
    rw [← hDdef] at hDs
    obtain ⟨Ni, hNNi⟩ := hNs.exists_right_inv
    obtain ⟨Di, hDDi⟩ := hDs.exists_right_inv
    have hNiN : Ni * N = 1 := hinvmat _ _ hNNi
    have hDiD : Di * D = 1 := hinvmat _ _ hDDi
    have hc0 : Commute (x + 1) (x - 1) := by
      show (x + 1) * (x - 1) = (x - 1) * (x + 1)
      noncomm_ring
    have hcND : Commute N D := by
      rw [hNdef, hDdef]
      exact Commute.add_left (Commute.add_right (Commute.refl _) (hc0.neg_right.smul_right _))
        (Commute.add_right (hc0.symm.smul_left _) (((Commute.refl (x - 1)).neg_right.smul_left _).smul_right _))
    have hσN : σ N = σ x * D := by
      rw [hNdef, hDdef, map_add, map_add, h1, hσF, map_sub, h1, mul_add, mul_add, mul_one, hσx,
        mul_smul_comm, mul_neg, mul_sub, mul_one, hσx, neg_sub, add_comm 1 (σ x)]
    have hσD : σ D = σ x * N := by
      rw [hNdef, hDdef, map_add, map_add, h1, hσF, map_neg, map_sub, h1, mul_add, mul_add, mul_one, hσx,
        mul_smul_comm, mul_sub, mul_one, hσx, neg_sub, add_comm 1 (σ x)]
    have hA : σ (N * Di) * (N * Di) = 1 := by
      calc σ (N * Di) * (N * Di) = σ Di * (σ x * ((D * N) * Di)) := by
            rw [hmul, hσN]; simp only [mul_assoc]
        _ = σ Di * (σ x * N) := by rw [← hcND.eq, mul_assoc N D Di, hDDi, mul_one]
        _ = σ Di * σ D := by rw [hσD]
        _ = 1 := by rw [← hmul, hDDi, h1]
    obtain ⟨ga, hga⟩ := hsurj _ hA
    have hDiN : Di * N = N * Di := by
      calc Di * N = Di * N * (D * Di) := by rw [hDDi, mul_one]
        _ = Di * (N * D) * Di := by simp only [mul_assoc]
        _ = Di * (D * N) * Di := by rw [hcND.eq]
        _ = N * Di := by rw [← mul_assoc Di D N, hDiD, one_mul]
    have hNiD : Ni * D = D * Ni := by
      calc Ni * D = Ni * D * (N * Ni) := by rw [hNNi, mul_one]
        _ = Ni * (D * N) * Ni := by simp only [mul_assoc]
        _ = Ni * (N * D) * Ni := by rw [hcND.eq]
        _ = D * Ni := by rw [← mul_assoc Ni N D, hNiN, one_mul]
    have hNeDf : N * e + D * f = (x + 1) + algebraMap F E s • ((x - 1) * (e - f)) := by
      have h0 : (x + 1) * e + (x + 1) * f = x + 1 := by rw [← mul_add, hef, mul_one]
      have h3 : N * e + D * f = ((x + 1) * e + (x + 1) * f) + algebraMap F E s • ((x - 1) * (e - f)) := by
        rw [hNdef, hDdef]
        simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg, smul_sub, smul_add, smul_neg, one_mul, mul_one, mul_assoc]
        abel
      rw [h3, h0]
    have hla : lam ga = 1 := by
      apply hcell
      have h0 : φ ga * e + f = Di * (N * e + D * f) := by
        rw [hga, mul_add, ← mul_assoc Di N e, ← mul_assoc Di D f, hDiD, one_mul, hDiN]
      rw [h0, hNeDf]
      exact (hunit_of _ _ hDiD).mul hIs
    have hgainv : φ ga⁻¹ = D * Ni := by
      have h0 : φ ga * φ ga⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have h3 : D * Ni * (N * Di) = 1 := by
        calc D * Ni * (N * Di) = D * (Ni * N) * Di := by simp only [mul_assoc]
          _ = 1 := by rw [hNiN, mul_one, hDDi]
      calc φ ga⁻¹ = D * Ni * (N * Di) * φ ga⁻¹ := by rw [h3, one_mul]
        _ = D * Ni := by rw [mul_assoc (D * Ni) (N * Di) (φ ga⁻¹), ← hga, h0, mul_one]
    have hDxeNf : D * x * e + N * f = (x + 1) * (x * e + f) + algebraMap F E s • ((x - 1) * (f - x * e)) := by
      rw [hNdef, hDdef]
      simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg, smul_sub, smul_add, smul_neg, one_mul, mul_one, mul_assoc]
      abel
    have hlb : lam (ga⁻¹ * g) = 1 := by
      apply hcell
      have h0 : φ (ga⁻¹ * g) * e + f = Ni * (D * x * e + N * f) := by
        rw [map_mul, hgainv, ← hx, mul_add, ← mul_assoc Ni N f, hNiN, one_mul, ← hNiD]
        simp only [mul_assoc]
      rw [h0, hDxeNf]
      exact (hunit_of _ _ hNiN).mul hIIs
    calc lam g = lam (ga * (ga⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = 1 := by rw [map_mul, hla, hlb, one_mul]
  obtain ⟨x, hx⟩ : ∃ x, x = φ g := ⟨_, rfl⟩
  have hσx : σ x * x = 1 := by rw [hx]; exact hu g
  have hxu : IsUnit x := hunit_of _ _ (hinvmat _ _ hσx)
  obtain ⟨ξi, hξi⟩ := hξ.exists_right_inv
  have S1 := fin1 (x + 1) (ξ • (x - 1)) ξi (by
    rw [smul_smul, mul_comm, hξi, one_smul, show x + 1 + (x - 1) = x + x by abel]
    exact htwo x hxu)
  have S2 := finE 1 (-ξ) 0 (by simp)
  have S3 := finE 1 ξ 0 (by simp)
  obtain ⟨t, ht⟩ := ((S1.union S2).union S3).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at ht
  obtain ⟨⟨ht1, ht2⟩, ht3⟩ := ht
  obtain ⟨w, hw⟩ : ∃ w : E, w = 1 + -ξ * algebraMap F E t := ⟨_, rfl⟩
  obtain ⟨cw, hcw⟩ : ∃ cw : E, cw = 1 + ξ * algebraMap F E t := ⟨_, rfl⟩
  rw [← hw] at ht2
  rw [← hcw] at ht3
  have hcw' : c w = cw := by rw [hw, hcw, map_add, map_one, map_mul, map_neg, hc, neg_neg, hcF]
  obtain ⟨wi, hwwi⟩ := ht2.exists_right_inv
  obtain ⟨z, hz⟩ : ∃ z : E, z = cw * wi := ⟨_, rfl⟩
  have hcwi : c wi * cw = 1 := by rw [← hcw', ← map_mul, mul_comm, hwwi, map_one]
  have hcz : c z * z = 1 := by
    have hccw : c cw = w := by rw [hw, hcw, map_add, map_one, map_mul, hc, hcF]
    rw [hz, map_mul, hccw]
    calc w * c wi * (cw * wi) = (c wi * cw) * (w * wi) := by ring
      _ = 1 := by rw [hcwi, hwwi, one_mul]
  have hzc : z * c z = 1 := by rw [mul_comm, hcz]
  have hzs : σ (z • (1 : Matrix β β E)) * (z • 1) = 1 := by
    rw [hsm, h1, smul_mul_smul_comm, mul_one, hcz, one_smul]
  obtain ⟨gz, hgz⟩ := hsurj _ hzs
  have hlz : lam gz = 1 := by
    apply hcell
    rw [hgz, smul_mul_assoc, one_mul]
    apply hunit_of _ (c z • e + f)
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, hee, hff, hef0, hfe0,
      smul_zero, add_zero, zero_add, hzc, hcz, one_smul, hef]
  have hlg' : lam (g * gz) = 1 := by
    apply main
    rw [map_mul, ← hx, hgz, mul_smul_comm, mul_one]
    have hwz : w * z = cw := by
      rw [hz]
      calc w * (cw * wi) = cw * (w * wi) := by ring
        _ = cw := by rw [hwwi, mul_one]
    have h0 : w • (z • x + 1) = (x + 1) + algebraMap F E t • (ξ • (x - 1)) := by
      rw [smul_add, smul_smul, hwz, hw, hcw]
      simp only [add_smul, one_smul, mul_smul, smul_sub, neg_mul, neg_smul, smul_comm ξ (algebraMap F E t)]
      abel
    have h1' : z • x + 1 = wi • (w • (z • x + 1)) := by
      rw [smul_smul, mul_comm wi w, hwwi, one_smul]
    rw [h1', h0]
    exact hsmul_unit wi _ (⟨⟨wi, w, by rw [mul_comm]; exact hwwi, hwwi⟩, rfl⟩ : IsUnit wi) ht1
  calc lam g = lam (g * gz) * (lam gz)⁻¹ := by rw [map_mul, mul_inv_cancel_right]
    _ = 1 := by rw [hlg', hlz, inv_one, one_mul]
end GlobalTheory.CompanionTheory.SiegelChar
