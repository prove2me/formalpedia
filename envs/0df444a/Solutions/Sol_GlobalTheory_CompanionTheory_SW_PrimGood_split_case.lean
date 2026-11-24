-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.split_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:33.923329+00:00
-- url     : https://prove2.me/submissions/815e46b5-e554-45b4-a7e7-79853d1c9f81

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_le_one_of_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_mul_ef
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_int_ef
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_mul_idm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_ev_idm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_idm_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ)
    (h2 : w (2 : L) = 1) (hΔ : w Δ = 1) {s : L} (hs : s * s = Δ)
    {M : ℕ} (y z : Fin M → K) (hz : z ⬝ᵥ y = 1) :
    ∃ (u : Kˣ) (z' : Fin M → K), (∀ k l, w (B.repr ((u : K) * y k) l) ≤ 1) ∧
      (∀ k l, w (B.repr (z' k) l) ≤ 1) ∧ ∑ k, z' k * ((u : K) * y k) = 1 := by
  have h20 : (2 : L) ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [h2]; exact one_ne_zero)
  have hws : w s = 1 := by
    have hq : w s ^ 2 = 1 := by rw [← map_pow, sq, hs, hΔ]
    refine le_antisymm (le_one_of_sq hq.le) ?_
    by_contra hc
    exact absurd hq (pow_lt_one₀ zero_le (not_le.1 hc) two_ne_zero).ne
  have hs0 : s ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [hws]; exact one_ne_zero)
  have hns : -s ≠ 0 := neg_ne_zero.2 hs0
  have hs' : -s * -s = Δ := by rw [neg_mul_neg, hs]
  set e : K := idm B s with he_def
  set f : K := idm B (-s) with hf_def
  have hef1 : e + f = 1 := idm_add h0 h20 hs0
  have me (x : K) : x * e = ev B s x • e := mul_idm h0 h1 h20 hs0 hs x
  have mf (x : K) : x * f = ev B (-s) x • f := mul_idm h0 h1 h20 hns hs' x
  have hee : e * e = e := by rw [me, (ev_idm h20 hs0).1, one_smul]
  have hff : f * f = f := by
    rw [mf]
    have := (ev_idm (B := B) h20 hns).1
    rw [this, one_smul]
  have hfe : f * e = 0 := by rw [me, (ev_idm h20 hs0).2, zero_smul]
  have hef : e * f = 0 := by rw [mul_comm, hfe]
  have hdec (x : K) : x = ev B s x • e + ev B (-s) x • f := by
    rw [← me, ← mf, ← mul_add, hef1, mul_one]
  have wi : w (2⁻¹ : L) = 1 := by rw [map_inv₀, h2, inv_one]
  have wi2 (t : L) (ht : w t = 1) : w ((2 * t)⁻¹ : L) = 1 := by
    rw [map_inv₀, map_mul, h2, ht, one_mul, inv_one]
  have hei (t : L) (ht : w t = 1) (l : Fin 2) : w (B.repr (idm B t) l) ≤ 1 := by
    have c := repr_coord B (2⁻¹ : L) ((2 * t)⁻¹ : L)
    unfold idm
    fin_cases l
    · simp only [Fin.zero_eta]; rw [c.1, wi]
    · simp only [Fin.mk_one]; rw [c.2, wi2 t ht]
  have he_int := hei s hws
  have hf_int := hei (-s) (by rw [Valuation.map_neg, hws])
  have h10 : (1 : K) ≠ 0 := h0 ▸ B.ne_zero 0
  have he0 : e ≠ 0 := fun h => by
    have := (ev_idm (B := B) h20 hs0).1
    rw [← he_def, h] at this
    simp [ev] at this
  have hf0 : f ≠ 0 := fun h => by
    have := (ev_idm (B := B) h20 hns).1
    rw [← hf_def, h] at this
    simp [ev] at this

  have hsum (g : K) (t : L) (mg : ∀ x, x * g = ev B t x • g) (hg : g ≠ 0) :
      ∃ k, ev B t (y k) ≠ 0 := by
    by_contra! hall
    apply hg
    calc g = (z ⬝ᵥ y) * g := by rw [hz, one_mul]
      _ = ∑ k, z k * (y k * g) := by simp only [dotProduct, Finset.sum_mul, mul_assoc]
      _ = 0 := by simp [mg, hall]
  obtain ⟨k₁, hk₁⟩ := hsum e s me he0
  obtain ⟨k₂, hk₂⟩ := hsum f (-s) mf hf0
  haveI : Nonempty (Fin M) := ⟨k₁⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => w (ev B s (y k)))
  obtain ⟨j, hj⟩ := Finite.exists_max (fun k => w (ev B (-s) (y k)))
  have hpi : ev B s (y i) ≠ 0 := by
    intro h
    have := hi k₁
    simp only [h, map_zero] at this
    exact hk₁ ((Valuation.zero_iff w).1 (le_antisymm this zero_le))
  have hqj : ev B (-s) (y j) ≠ 0 := by
    intro h
    have := hj k₂
    simp only [h, map_zero] at this
    exact hk₂ ((Valuation.zero_iff w).1 (le_antisymm this zero_le))
  set p : Fin M → L := fun k => ev B s (y k) with hp
  set q : Fin M → L := fun k => ev B (-s) (y k) with hq
  have hpi' : p i ≠ 0 := hpi
  have hqj' : q j ≠ 0 := hqj
  have huv : ((p i)⁻¹ • e + (q j)⁻¹ • f) * (p i • e + q j • f) = 1 := by
    rw [mul_ef hee hff hef, inv_mul_cancel₀ hpi', inv_mul_cancel₀ hqj', one_smul, one_smul, hef1]
  have huy (k : Fin M) : ((p i)⁻¹ • e + (q j)⁻¹ • f) * y k =
      ((p i)⁻¹ * p k) • e + ((q j)⁻¹ * q k) • f := by
    rw [← mul_ef hee hff hef, ← hdec (y k)]
  have hle (t₀ t : L) (h : w t ≤ w t₀) (h0 : t₀ ≠ 0) : w (t₀⁻¹ * t) ≤ 1 := by
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 h0)), mul_one]
    exact h
  refine ⟨⟨(p i)⁻¹ • e + (q j)⁻¹ • f, p i • e + q j • f, huv, by rw [mul_comm]; exact huv⟩,
    Pi.single i e + Pi.single j f, ?_, ?_, ?_⟩
  · intro k l
    simp only [Units.val_mk]
    rw [huy]
    exact int_ef w he_int hf_int (hle _ _ (hi k) hpi') (hle _ _ (hj k) hqj') l
  · intro k l
    have hz0 : ∀ l, w (B.repr (0 : K) l) ≤ 1 := fun l => by simp
    have h1' : ∀ (g : K) (m : Fin M), (∀ l, w (B.repr g l) ≤ 1) →
        w (B.repr ((Pi.single m g : Fin M → K) k) l) ≤ 1 := by
      intro g m hg
      by_cases hk : k = m
      · subst hk; simpa using hg l
      · simp [Pi.single_apply, hk]
    simp only [Pi.add_apply, map_add, Finsupp.add_apply]
    exact (w.map_add _ _).trans (max_le (h1' e i he_int) (h1' f j hf_int))
  · simp only [Units.val_mk, Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, huy]
    have a1 : e * (((p i)⁻¹ * p i) • e + ((q j)⁻¹ * q i) • f) = e := by
      rw [inv_mul_cancel₀ hpi', one_smul, mul_add, hee, mul_smul_comm, hef, smul_zero, add_zero]
    have a2 : f * (((p i)⁻¹ * p j) • e + ((q j)⁻¹ * q j) • f) = f := by
      rw [inv_mul_cancel₀ hqj', one_smul, mul_add, hff, mul_smul_comm, hfe, smul_zero, zero_add]
    rw [a1, a2, hef1]
end GlobalTheory.CompanionTheory.SW.PrimGood
