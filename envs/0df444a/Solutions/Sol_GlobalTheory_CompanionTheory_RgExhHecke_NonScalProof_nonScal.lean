-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:15.894643+00:00
-- url     : https://prove2.me/submissions/fc101e2e-c524-416c-971b-e253b3779f84

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_isPolynomial_capelliMinor
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_coeff_extract
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_om_nnPlus
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_qdetEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_expand_minus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
theorem _root_.solution : NonScal := by
  intro n X χ s hS hN hfree ⟨r, hrs, hr⟩
  cases n with
  | zero => exact s.elim0
  | succ m =>
  have hE' : GlRelR X.E := X.gl
  set ω : ℂ := cn (m + 1) - χ s with hω

  have hC : ∀ x : ℂ, capelliC X.E x = Formalism.QuantumDeterminants.capP χ (x - cn (m + 1)) • (1 : Module.End ℂ X.V) := by
    intro x
    have h := hS (x - cn (m + 1))
    have e : x - cn (m + 1) + (((m + 1 : ℕ) : ℂ) - 1) / 2 = x := by simp [cn]
    rw [e, GlobalTheory.CompanionTheory.RgExhHecke.qdetEq] at h
    exact h

  set P : ℂ[X] := ∏ q : Fin (m + 1), (Polynomial.X + C (χ q - χ s)) with hPdef
  have hPe : ∀ t : ℂ, P.eval t = Formalism.QuantumDeterminants.capP χ (ω + t - cn (m + 1)) := by
    intro t
    simp only [hPdef, eval_prod, eval_add, eval_X, eval_C, Formalism.QuantumDeterminants.capP]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hω]; ring
  have hPd : (Polynomial.X : ℂ[X]) ^ 2 ∣ P := by
    have hs : s ∈ (univ : Finset (Fin (m + 1))) := mem_univ s
    have hr' : r ∈ (univ.erase s) := mem_erase.2 ⟨hrs, mem_univ r⟩
    rw [hPdef, ← Finset.mul_prod_erase univ _ hs, ← Finset.mul_prod_erase _ _ hr', hr, sub_self, C_0, add_zero,
      ← mul_assoc, pow_two]
    exact Dvd.intro _ rfl

  obtain ⟨v, hv⟩ := exists_ne (0 : X.V)
  have hc1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) ≠ 0 := by
    simp only [Formalism.QuantumDeterminants.capP]
    refine Finset.prod_ne_zero_iff.2 fun q _ hq => hfree q ?_
    rw [hω] at hq
    linear_combination hq
  obtain ⟨d, hd⟩ : ∃ d : Fin (m + 1), cminor X.E s.succAbove d.succAbove (ω - 1) v ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h := LinearMap.congr_fun (capelli_expand_minus X.E hE' (ω - 1) s s) v
    rw [LinearMap.sum_apply, if_pos rfl, hC] at h
    have h0 : ∑ d : Fin (m + 1), (((-1 : ℂ) ^ ((d : ℕ) + (s : ℕ))) •
        (capEntry X.E (ω - 1 - (m : ℂ)) s d * cminor X.E s.succAbove d.succAbove (ω - 1))) v = 0 :=
      Finset.sum_eq_zero fun d _ => by simp [Module.End.mul_apply, hall d]
    rw [h0] at h
    have h1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) • v = 0 := by simpa using h.symm
    exact (smul_ne_zero hc1 hv) h1
  set y : Fin (m + 1) → ℂ := Pi.single d 1 with hy
  choose p hp using fun a b : Fin (m + 1) => isPolynomial_capelliMinor X.E a.succAbove b.succAbove (ω - 1)
  set k : ℕ := (univ.sup fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree) + 2 with hk
  have hdeg : ∀ a b, (p a b).natDegree < k := fun a b => by
    have := Finset.le_sup (f := fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree)
      (mem_univ (a, b))
    simp only at this
    omega
  set w : ℕ → Fin (m + 1) → X.V :=
    fun i a => ∑ c, (y c * (-1) ^ ((a : ℕ) + (c : ℕ))) • ((p a c).coeff i) v with hw
  have hexp : ∀ (a c : Fin (m + 1)) (t : ℂ), cminor X.E a.succAbove c.succAbove (ω + t - 1) v =
      ∑ i ∈ range k, t ^ i • ((p a c).coeff i) v := by
    intro a c t
    have e : ω + t - 1 = ω - 1 + t := by ring
    have hp' : cminor X.E a.succAbove c.succAbove (ω - 1 + t) = _ := hp a c t
    rw [e, hp', eval_eq_sum_range' (hdeg a c), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  have hNt : ∀ t : ℂ, nnPlus X.E y (ω + t) v = ∑ i ∈ range k, t ^ i • w i := by
    intro t
    funext a
    simp only [nnPlus, hexp, Finset.sum_apply, Pi.smul_apply, hw, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => smul_comm _ _ _
  set T : Module.End ℂ (Fin (m + 1) → X.V) := om X + ω • 1 with hT
  have hid : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i =
      P.eval t • (fun b => y b • v) := by
    intro t
    rw [← hNt]
    have h := om_nnPlus X y (ω + t) v
    have e : T (nnPlus X.E y (ω + t) v) + t • nnPlus X.E y (ω + t) v =
        om X (nnPlus X.E y (ω + t) v) + (ω + t) • nnPlus X.E y (ω + t) v := by
      simp [hT, add_smul, add_assoc]
    rw [e, h, hC, ← hPe]
    funext b
    simp only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply]
    exact smul_comm _ _ _
  obtain ⟨h0, h1⟩ := coeff_extract T k (by omega) w P _ hPd hid
  have hw0 : w 0 = nnPlus X.E y ω v := by
    have := hNt 0
    rw [add_zero] at this
    rw [this, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (mem_range.2 (by omega)) h
  have hw0ne : w 0 ≠ 0 := by
    intro h
    rw [hw0] at h
    have h2 := congrFun h s
    simp only [nnPlus, Pi.zero_apply] at h2
    rw [Finset.sum_eq_single d] at h2
    · simp [hy] at h2
      exact hd h2
    · intro c _ hc; simp [hy, hc]
    · simp
  have hTa : ∀ f, T f = 0 ↔ om X f = (χ s - cn (m + 1)) • f := by
    intro f
    have : χ s - cn (m + 1) = -ω := by rw [hω]; ring
    rw [this, hT, neg_smul, eq_neg_iff_add_eq_zero]
    simp
  refine ⟨w 1, ?_, fun h => hw0ne ?_⟩
  · have ha : χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2 = -ω := by rw [hω]; simp [cn]
    show w 1 ∈ (om X).maxGenEigenspace (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2)
    rw [ha, Module.End.mem_maxGenEigenspace]
    refine ⟨2, ?_⟩
    have e : om X - (-ω) • (1 : Module.End ℂ (Fin (m + 1) → X.V)) = T := by simp [hT]
    have e2 : T (w 1) = - w 0 := eq_neg_of_add_eq_zero_left h1
    rw [e, pow_two, Module.End.mul_apply, e2, map_neg, h0, neg_zero]
  · have := (hTa _).2 h
    rw [this, zero_add] at h1
    exact h1
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
