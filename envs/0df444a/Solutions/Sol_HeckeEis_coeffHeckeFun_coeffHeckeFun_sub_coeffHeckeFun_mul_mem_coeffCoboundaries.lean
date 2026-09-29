-- Prove2me | solution 1 for HeckeEis.coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/40580124-e3eb-5e6e-914b-09f492fce41b

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Theorems.Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "heckeConjMat heckeConjMat_apply_zero_one heckeConjMat_apply_one_zero heckeUpper mem_heckeUpper heckeConj transferAux coeffCocycles coeffCoboundaries coeffHeckeFun coeffHeckeFun_apply sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries coeffHeckeFun_mem_coeffCoboundaries"
p2m_open "HeckeEis"
namespace R2CompTT

open CongruenceSubgroup Matrix
open scoped MatrixGroups

section Entries

variable (N ℓ : ℕ) [NeZero ℓ]

theorem conj_apply00 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 0 0 = ((u : Gamma0 N) : SL(2, ℤ)) 0 0 := rfl

theorem conj_apply01 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 0 1 = ((u : Gamma0 N) : SL(2, ℤ)) 0 1 / (ℓ : ℤ) := rfl

theorem conj_apply10 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 1 0 = ((u : Gamma0 N) : SL(2, ℤ)) 1 0 * (ℓ : ℤ) := rfl

theorem conj_apply11 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 1 1 = ((u : Gamma0 N) : SL(2, ℤ)) 1 1 := rfl

theorem dvd_conj_apply10 (u : ↥(heckeUpper N ℓ)) :
    (ℓ : ℤ) ∣ ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 1 0 := by
  rw [conj_apply10]; exact dvd_mul_left _ _

end Entries

section Levels

variable (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m]

omit [NeZero ℓ] [NeZero ℓ'] [NeZero m] in
theorem heckeUpper_le_left (hm : m = ℓ * ℓ') : heckeUpper N m ≤ heckeUpper N ℓ := by
  intro w hw
  rw [mem_heckeUpper] at hw ⊢
  have h : (ℓ : ℤ) ∣ (m : ℤ) := ⟨(ℓ' : ℤ), by rw [hm]; push_cast; ring⟩
  exact h.trans hw

omit [NeZero ℓ] [NeZero ℓ'] [NeZero m] in
theorem heckeUpper_le_right (hm : m = ℓ * ℓ') : heckeUpper N m ≤ heckeUpper N ℓ' := by
  intro w hw
  rw [mem_heckeUpper] at hw ⊢
  have h : (ℓ' : ℤ) ∣ (m : ℤ) := ⟨(ℓ : ℤ), by rw [hm]; push_cast; ring⟩
  exact h.trans hw

theorem mem_heckeUpper_mul_iff (hm : m = ℓ * ℓ') (u : ↥(heckeUpper N ℓ)) :
    (u : Gamma0 N) ∈ heckeUpper N m ↔ heckeConj N ℓ u ∈ heckeUpper N ℓ' := by
  rw [mem_heckeUpper, mem_heckeUpper, conj_apply01]
  obtain ⟨b', hb'⟩ := (mem_heckeUpper N ℓ).mp u.2
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  rw [hb', Int.mul_ediv_cancel_left _ hℓ0, hm, Nat.cast_mul]
  exact mul_dvd_mul_iff_left hℓ0

def toLeft (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) : ↥(heckeUpper N ℓ) :=
  ⟨w, heckeUpper_le_left N ℓ ℓ' m hm w.2⟩

@[scoped simp] theorem coe_toLeft (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    ((toLeft N ℓ ℓ' m hm w : ↥(heckeUpper N ℓ)) : Gamma0 N) = w := rfl

theorem conj_toLeft_mem (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    heckeConj N ℓ (toLeft N ℓ ℓ' m hm w) ∈ heckeUpper N ℓ' :=
  (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mp w.2

theorem heckeConj_mul (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    heckeConj N m w =
      heckeConj N ℓ' ⟨heckeConj N ℓ (toLeft N ℓ ℓ' m hm w), conj_toLeft_mem N ℓ ℓ' m hm w⟩ := by
  have hm' : ((m : ℕ) : ℤ) = (ℓ : ℤ) * (ℓ' : ℤ) := by rw [hm, Nat.cast_mul]
  refine Subtype.ext (Subtype.ext ?_)
  change heckeConjMat m (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    = heckeConjMat ℓ' (heckeConjMat ℓ (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
  set A : Matrix (Fin 2) (Fin 2) ℤ := (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simp only [heckeConjMat_apply_zero_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [Int.ediv_ediv_of_nonneg (by positivity), hm']
  · simp only [heckeConjMat_apply_one_zero, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [hm', mul_assoc]
  · rfl

theorem heckeConj_mul_eq (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) (u : ↥(heckeUpper N ℓ))
    (u' : ↥(heckeUpper N ℓ')) (hwu : (w : Gamma0 N) = u) (huu' : heckeConj N ℓ u = (u' : Gamma0 N)) :
    heckeConj N m w = heckeConj N ℓ' u' := by
  rw [heckeConj_mul N ℓ ℓ' m hm w]
  congr 1
  refine Subtype.ext ?_
  rw [← huu']
  change heckeConj N ℓ (toLeft N ℓ ℓ' m hm w) = heckeConj N ℓ u
  congr 1
  exact Subtype.ext hwu

end Levels

section Coset

variable (N ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

theorem exists_heckeConj_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (x : Gamma0 N)
    (hx : (ℓ : ℤ) ∣ (x : SL(2, ℤ)) 1 0) : ∃ u : ↥(heckeUpper N ℓ), heckeConj N ℓ u = x := by
  obtain ⟨c', hc'⟩ := hx
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  set A : Matrix (Fin 2) (Fin 2) ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hA]; exact (x : SL(2, ℤ)).2
  have hc'' : A 1 0 = (ℓ : ℤ) * c' := hc'

  let B : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0, A 0 1 * (ℓ : ℤ); c', A 1 1]
  have hB00 : B 0 0 = A 0 0 := rfl
  have hB01 : B 0 1 = A 0 1 * (ℓ : ℤ) := rfl
  have hB10 : B 1 0 = c' := rfl
  have hB11 : B 1 1 = A 1 1 := rfl
  have hBdet : B.det = 1 := by
    rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11, ← hdet, hc'']; ring

  have hNc : ((A 1 0 : ℤ) : ZMod N) = 0 := by
    have := Gamma0_mem.mp x.2
    simpa [hA] using this
  have hNc' : ((c' : ℤ) : ZMod N) = 0 := by
    have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
    have hdvd : (N : ℤ) ∣ (ℓ : ℤ) * c' := by
      rw [← hc'']; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hNc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr (hcop.dvd_of_dvd_mul_left hdvd)
  let uSL : SL(2, ℤ) := ⟨B, hBdet⟩
  have huG : uSL ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact hNc'
  have huU : (⟨uSL, huG⟩ : Gamma0 N) ∈ heckeUpper N ℓ := by
    rw [mem_heckeUpper]
    exact Dvd.intro_left _ rfl
  refine ⟨⟨⟨uSL, huG⟩, huU⟩, Subtype.ext (Subtype.ext ?_)⟩
  change heckeConjMat ℓ B = A
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simp only [heckeConjMat_apply_zero_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, hB01]
    exact Int.mul_ediv_cancel _ hℓ0
  · simp only [heckeConjMat_apply_one_zero, Fin.zero_eta, Fin.mk_one, Fin.isValue, hB10, hc'']
    ring
  · rfl

theorem exists_mul_mem_dvd (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) (k : ℤ)
    (he : ¬ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * k * (ℓ' : ℤ) + (γ : SL(2, ℤ)) 1 1) :
    ∃ u'' : ↥(heckeUpper N ℓ'), (ℓ : ℤ) ∣ ((γ : Gamma0 N) * u'' : SL(2, ℤ)) 1 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set c : ℤ := (γ : SL(2, ℤ)) 1 0 with hc
  set d : ℤ := (γ : SL(2, ℤ)) 1 1 with hd
  set e : ℤ := c * k * (ℓ' : ℤ) + d with he_def
  have heZ : ((e : ℤ) : ZMod ℓ) ≠ 0 := fun h => he ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h)
  have hNZ : ((N : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
    exact hℓN h
  set Y : ZMod ℓ := -(c : ZMod ℓ) * (((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ))⁻¹ with hY
  let z₁ : ℕ := Y.val
  let zz : ℤ := (N : ℤ) * (z₁ : ℤ)
  have hz₁ : ((z₁ : ℤ) : ZMod ℓ) = Y := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val Y
  have hzz : ((zz : ℤ) : ZMod ℓ) = ((N : ℤ) : ZMod ℓ) * Y := by
    change (((N : ℤ) * (z₁ : ℤ) : ℤ) : ZMod ℓ) = _
    rw [Int.cast_mul, hz₁]
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![1 + k * (ℓ' : ℤ) * zz, k * (ℓ' : ℤ); zz, 1]
  have hB00 : B 0 0 = 1 + k * (ℓ' : ℤ) * zz := rfl
  have hB01 : B 0 1 = k * (ℓ' : ℤ) := rfl
  have hB10 : B 1 0 = zz := rfl
  have hB11 : B 1 1 = 1 := rfl
  have hBdet : B.det = 1 := by rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11]; ring
  let uSL : SL(2, ℤ) := ⟨B, hBdet⟩
  have huG : uSL ∈ Gamma0 N := by
    rw [Gamma0_mem]
    change ((B 1 0 : ℤ) : ZMod N) = 0
    rw [hB10]
    change (((N : ℤ) * (z₁ : ℤ) : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  have huU : (⟨uSL, huG⟩ : Gamma0 N) ∈ heckeUpper N ℓ' := by
    rw [mem_heckeUpper]
    change (ℓ' : ℤ) ∣ B 0 1
    rw [hB01]; exact dvd_mul_left _ _
  refine ⟨⟨⟨uSL, huG⟩, huU⟩, ?_⟩

  have hentry : ((γ : Gamma0 N) * (⟨⟨uSL, huG⟩, huU⟩ : ↥(heckeUpper N ℓ')) : SL(2, ℤ)) 1 0
      = c * (1 + k * (ℓ' : ℤ) * zz) + d * zz := by
    change (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * B) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, hB00, hB10]
  rw [hentry, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_one, hzz]
  have hNe : ((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ) ≠ 0 := mul_ne_zero hNZ heZ
  have hX : (((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ)) * Y = -(c : ZMod ℓ) := by
    rw [hY, mul_comm, mul_assoc, inv_mul_cancel₀ hNe, mul_one]
  have he' : ((e : ℤ) : ZMod ℓ) = (c : ZMod ℓ) * (k : ZMod ℓ) * ((ℓ' : ℤ) : ZMod ℓ) + (d : ZMod ℓ) := by
    rw [he_def, Int.cast_add, Int.cast_mul, Int.cast_mul]
  linear_combination hX - (((N : ℤ) : ZMod ℓ) * Y) * he'

theorem exists_conj_mul_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓℓ' : ¬ ℓ ∣ ℓ') (γ : Gamma0 N) :
    ∃ (u : ↥(heckeUpper N ℓ)) (u' : ↥(heckeUpper N ℓ')),
      (heckeConj N ℓ u : Gamma0 N) * u' = γ := by

  have hk : ∃ k : ℤ, ¬ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * k * (ℓ' : ℤ) + (γ : SL(2, ℤ)) 1 1 := by
    by_cases hd : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 1
    · refine ⟨1, fun h => ?_⟩
      rw [mul_one] at h
      have hc : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * (ℓ' : ℤ) := (dvd_add_left hd).mp h
      have hℓp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
      rcases hℓp.dvd_or_dvd hc with h1 | h1
      ·
        have hdet := Matrix.det_fin_two ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        rw [(γ : SL(2, ℤ)).2] at hdet
        have : (ℓ : ℤ) ∣ 1 := by
          rw [hdet]
          exact dvd_sub (hd.mul_left _) (h1.mul_left _)
        exact hℓ.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
      · exact hℓℓ' (by exact_mod_cast h1)
    · exact ⟨0, by simpa using hd⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨u'', hu''⟩ := exists_mul_mem_dvd N ℓ ℓ' hℓ hℓN γ k hk
  obtain ⟨u, hu⟩ := exists_heckeConj_eq N ℓ hℓ hℓN ((γ : Gamma0 N) * u'') hu''
  refine ⟨u, u''⁻¹, ?_⟩
  rw [hu, Subgroup.coe_inv, mul_inv_cancel_right]

theorem exists_section (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓℓ' : ¬ ℓ ∣ ℓ') :
    ∃ σ : Gamma0 N ⧸ heckeUpper N ℓ' → ↥(heckeUpper N ℓ),
      ∀ q', ((heckeConj N ℓ (σ q') : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := by
  have h : ∀ q' : Gamma0 N ⧸ heckeUpper N ℓ', ∃ u : ↥(heckeUpper N ℓ),
      ((heckeConj N ℓ u : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := by
    intro q'
    obtain ⟨u, u', huu'⟩ := exists_conj_mul_eq N ℓ ℓ' hℓ hℓN hℓℓ' q'.out
    refine ⟨u, ?_⟩
    rw [← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.mpr ?_
    rw [← huu', inv_mul_cancel_left]
    exact u'.2
  choose σ hσ using h
  exact ⟨σ, hσ⟩

end Coset

section Main

variable {N ℓ ℓ' m : ℕ} [NeZero ℓ] [NeZero ℓ'] [NeZero m]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (a a' : V →ₗ[K] V)
variable (σ : Gamma0 N ⧸ heckeUpper N ℓ' → ↥(heckeUpper N ℓ))
variable (hσ : ∀ q', ((heckeConj N ℓ (σ q') : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q')

def sP (q' : Gamma0 N ⧸ heckeUpper N ℓ') : Gamma0 N := heckeConj N ℓ (σ q')

include hσ in
theorem sP_coe (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := hσ q'

def tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') : ↥(heckeUpper N ℓ') :=
  ⟨(sP σ (h • q'))⁻¹ * (h * sP σ q'), by
    refine QuotientGroup.eq.mp ?_
    rw [sP_coe σ hσ]
    change h • q' = h • ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ')
    rw [sP_coe σ hσ]⟩

@[scoped simp] theorem coe_tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((tP σ hσ h q' : ↥(heckeUpper N ℓ')) : Gamma0 N) = (sP σ (h • q'))⁻¹ * (h * sP σ q') := rfl

theorem sP_mul_tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    sP σ (h • q') * (tP σ hσ h q' : Gamma0 N) = h * sP σ q' := by
  rw [coe_tP, mul_inv_cancel_left]

noncomputable def Ty (z : Gamma0 N → V) : Gamma0 N → V := fun h =>
  letI := (heckeUpper N ℓ').fintypeQuotientOfFiniteIndex
  ∑ q' : Gamma0 N ⧸ heckeUpper N ℓ', ρ (sP σ (h • q')) (a' (z (heckeConj N ℓ' (tP σ hσ h q'))))

theorem Ty_sub_mem
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    Ty ρ a' σ hσ z - coeffHeckeFun N ℓ' ρ a' z ∈ coeffCoboundaries ρ :=
  sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries N ℓ' ρ a' ha' (sP σ) (tP σ hσ)
    (sP_coe σ hσ) (sP_mul_tP σ hσ) hz

noncomputable def PsiFun (x : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ')) :
    Gamma0 N ⧸ heckeUpper N m :=
  ((x.1.out * ((σ x.2 : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)

variable (hm : m = ℓ * ℓ')

include hσ hm in
theorem PsiFun_injective : Function.Injective (PsiFun (m := m) σ) := by
  rintro ⟨q₁, q₁'⟩ ⟨q₂, q₂'⟩ h
  have hW : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
      * (q₂.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N)) ∈ heckeUpper N m :=
    QuotientGroup.eq.mp h

  have hU : q₁.out⁻¹ * q₂.out ∈ heckeUpper N ℓ := by
    have h1 : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
        * (q₂.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N)) ∈ heckeUpper N ℓ :=
      heckeUpper_le_left N ℓ ℓ' m hm hW
    rw [_root_.mul_inv_rev, mul_assoc, ← mul_assoc (q₁.out⁻¹)] at h1
    have h2 := (Subgroup.mul_mem_cancel_left _ ((heckeUpper N ℓ).inv_mem (σ q₁').2)).mp h1
    exact (Subgroup.mul_mem_cancel_right _ (σ q₂').2).mp h2
  have hq : q₁ = q₂ := by
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.mpr hU
  subst hq
  have hW' : (((σ q₁')⁻¹ * σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
    have : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
        * (q₁.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N))
        = (((σ q₁')⁻¹ * σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
      push_cast; group
    rw [← this]; exact hW
  have hU' : heckeConj N ℓ ((σ q₁')⁻¹ * σ q₂') ∈ heckeUpper N ℓ' :=
    (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mp hW'
  rw [map_mul, map_inv] at hU'
  have hq' : ((sP σ q₁' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = (sP σ q₂' : Gamma0 N) :=
    QuotientGroup.eq.mpr hU'
  rw [sP_coe σ hσ, sP_coe σ hσ] at hq'
  rw [hq']

include hσ hm in
theorem PsiFun_surjective : Function.Surjective (PsiFun (m := m) σ) := by
  intro Q
  induction Q using QuotientGroup.induction_on with
  | H γ =>
    set q : Gamma0 N ⧸ heckeUpper N ℓ := (γ : Gamma0 N ⧸ heckeUpper N ℓ) with hq
    have hu₀ : q.out⁻¹ * γ ∈ heckeUpper N ℓ := QuotientGroup.eq.mp (by rw [QuotientGroup.out_eq'])
    set u₀ : ↥(heckeUpper N ℓ) := ⟨q.out⁻¹ * γ, hu₀⟩ with hu₀_def
    set q' : Gamma0 N ⧸ heckeUpper N ℓ' :=
      ((heckeConj N ℓ u₀ : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') with hq'
    refine ⟨(q, q'), ?_⟩
    change ((q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)
      = (γ : Gamma0 N ⧸ heckeUpper N m)
    refine QuotientGroup.eq.mpr ?_
    have hmem : (((σ q')⁻¹ * u₀ : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
      refine (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mpr ?_
      rw [map_mul, map_inv]
      refine QuotientGroup.eq.mp ?_
      change ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q'
      exact sP_coe σ hσ q'
    have : (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹ * γ
        = (((σ q')⁻¹ * u₀ : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
      rw [hu₀_def]; push_cast; group
    rw [this]; exact hmem

noncomputable def Psi : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ') ≃
    Gamma0 N ⧸ heckeUpper N m :=
  Equiv.ofBijective (PsiFun σ) ⟨PsiFun_injective σ hσ hm, PsiFun_surjective σ hσ hm⟩

theorem Psi_apply (x : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ')) :
    Psi σ hσ hm x =
      ((x.1.out * ((σ x.2 : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m) :=
  rfl

noncomputable def wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ↥(heckeUpper N ℓ) :=
  (σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q'))⁻¹
    * transferAux (heckeUpper N ℓ) g q * σ q'

theorem heckeConj_wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ)
    (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    heckeConj N ℓ (wU σ g q q') =
      (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q' : Gamma0 N) := by
  rw [wU, map_mul, map_mul, map_inv, coe_tP, mul_assoc]
  rfl

include hσ hm in
theorem wU_mem (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
  refine (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mpr ?_
  rw [heckeConj_wU σ hσ]
  exact (tP σ hσ _ q').2

theorem coe_wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) =
      ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N)⁻¹
        * ((g • q).out⁻¹ * (g * q.out)) * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := rfl

theorem smul_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    g • Psi σ hσ hm (q, q') =
      Psi σ hσ hm (g • q, (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') := by
  rw [Psi_apply, Psi_apply]
  change (((g * (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N))) : Gamma0 N) :
      Gamma0 N ⧸ heckeUpper N m) = _
  refine QuotientGroup.eq.mpr ?_
  have key : ((g • q).out *
        ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹ * (g * (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N)))
      = ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
    rw [coe_wU]; group
  have hmem := (heckeUpper N m).inv_mem (wU_mem σ hσ hm g q q')
  rw [← key, _root_.mul_inv_rev, inv_inv] at hmem
  exact hmem

noncomputable def SS (Q : Gamma0 N ⧸ heckeUpper N m) : Gamma0 N :=
  ((Psi σ hσ hm).symm Q).1.out * (((σ ((Psi σ hσ hm).symm Q).2) : ↥(heckeUpper N ℓ)) : Gamma0 N)

theorem SS_Psi (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    SS σ hσ hm (Psi σ hσ hm (q, q')) = q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
  rw [SS, Equiv.symm_apply_apply]

theorem SS_coe (Q : Gamma0 N ⧸ heckeUpper N m) :
    ((SS σ hσ hm Q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m) = Q := by
  conv_rhs => rw [← (Psi σ hσ hm).apply_symm_apply Q]
  unfold SS
  rw [Psi_apply]

noncomputable def TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) : ↥(heckeUpper N m) :=
  ⟨(SS σ hσ hm (g • Q))⁻¹ * (g * SS σ hσ hm Q), by
    refine QuotientGroup.eq.mp ?_
    rw [SS_coe]
    change g • Q = g • ((SS σ hσ hm Q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)
    rw [SS_coe]⟩

@[scoped simp] theorem coe_TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) :
    ((TT σ hσ hm g Q : ↥(heckeUpper N m)) : Gamma0 N) = (SS σ hσ hm (g • Q))⁻¹ * (g * SS σ hσ hm Q) :=
  rfl

theorem SS_mul_TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) :
    SS σ hσ hm (g • Q) * (TT σ hσ hm g Q : Gamma0 N) = g * SS σ hσ hm Q := by
  rw [coe_TT, mul_inv_cancel_left]

theorem coe_TT_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((TT σ hσ hm g (Psi σ hσ hm (q, q')) : ↥(heckeUpper N m)) : Gamma0 N)
      = ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
  rw [coe_TT, smul_Psi, SS_Psi, SS_Psi, coe_wU]
  group

theorem heckeConj_TT_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ)
    (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    heckeConj N m (TT σ hσ hm g (Psi σ hσ hm (q, q'))) =
      heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q') :=
  heckeConj_mul_eq N ℓ ℓ' m hm _ (wU σ g q q') _ (coe_TT_Psi σ hσ hm g q q') (heckeConj_wU σ hσ g q q')

noncomputable def TmS (z : Gamma0 N → V) : Gamma0 N → V := fun g =>
  letI := (heckeUpper N m).fintypeQuotientOfFiniteIndex
  ∑ Q : Gamma0 N ⧸ heckeUpper N m, ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g Q))))

include hm in

theorem compat_mul
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    (w : ↥(heckeUpper N m)) :
    (a ∘ₗ a') ∘ₗ ρ (heckeConj N m w) = ρ (w : Gamma0 N) ∘ₗ (a ∘ₗ a') := by
  rw [heckeConj_mul N ℓ ℓ' m hm w, LinearMap.comp_assoc, ha', ← LinearMap.comp_assoc]
  change (a ∘ₗ ρ (heckeConj N ℓ (toLeft N ℓ ℓ' m hm w))) ∘ₗ a' = _
  rw [ha, LinearMap.comp_assoc]
  rfl

theorem TmS_sub_mem
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    TmS ρ a a' σ hσ hm z - coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ coeffCoboundaries ρ :=
  sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries N m ρ (a ∘ₗ a') (compat_mul ρ a a' hm ha ha')
    (SS σ hσ hm) (TT σ hσ hm) (SS_coe σ hσ hm) (SS_mul_TT σ hσ hm) hz

theorem coeffHeckeFun_Ty
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (z : Gamma0 N → V) :
    coeffHeckeFun N ℓ ρ a (Ty ρ a' σ hσ z) = TmS ρ a a' σ hσ hm z := by
  letI iU := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  letI iU' := (heckeUpper N ℓ').fintypeQuotientOfFiniteIndex
  letI iW := (heckeUpper N m).fintypeQuotientOfFiniteIndex
  funext g
  rw [coeffHeckeFun_apply]
  change ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, ρ (g • q).out (a (Ty ρ a' σ hσ z _)) =
    ∑ Q : Gamma0 N ⧸ heckeUpper N m, ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g Q))))

  rw [← Fintype.sum_equiv (Psi σ hσ hm) (fun x => ρ (SS σ hσ hm (g • Psi σ hσ hm x))
      ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g (Psi σ hσ hm x))))))
      (fun Q => ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g Q)))))
      (fun x => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_

  simp only [Ty, map_sum]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hpush : a (ρ (sP σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q'))
      (a' (z (heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q')))))
      = ρ ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N)
        (a (a' (z (heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q'))))) :=
    LinearMap.congr_fun (ha _) _
  rw [hpush, smul_Psi, SS_Psi, heckeConj_TT_Psi, map_mul, Module.End.mul_apply, LinearMap.comp_apply]

theorem coeffHeckeFun_sub (ℓ₀ : ℕ) [NeZero ℓ₀] (b : V →ₗ[K] V) (z w : Gamma0 N → V) :
    coeffHeckeFun N ℓ₀ ρ b (z - w) = coeffHeckeFun N ℓ₀ ρ b z - coeffHeckeFun N ℓ₀ ρ b w := by
  letI := (heckeUpper N ℓ₀).fintypeQuotientOfFiniteIndex
  funext g
  simp only [coeffHeckeFun_apply, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

end Main

end R2CompTT
p2m_reactivate "P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis.R2CompTT"
end HeckeEis
p2m_reactivate "P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis.R2CompTT P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis"

open scoped MatrixGroups in
theorem solution
    (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓℓ' : ¬ ℓ ∣ ℓ') (hm : m = ℓ * ℓ')
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a a' : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(HeckeEis.heckeUpper N ℓ'),
      a' ∘ₗ ρ (HeckeEis.heckeConj N ℓ' u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a')
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a (HeckeEis.coeffHeckeFun N ℓ' ρ a' z)
      - HeckeEis.coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ HeckeEis.coeffCoboundaries ρ := by
  open _root_.HeckeEis _root_.P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis HeckeEis.R2CompTT in
  obtain ⟨σ, hσ⟩ := exists_section N ℓ ℓ' hℓ hℓN hℓℓ'

  have h1 : coeffHeckeFun N ℓ ρ a (Ty ρ a' σ hσ z - coeffHeckeFun N ℓ' ρ a' z) ∈ coeffCoboundaries ρ :=
    coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha (Ty_sub_mem ρ a' σ hσ ha' hz)
  have h2 : coeffHeckeFun N ℓ ρ a (Ty ρ a' σ hσ z) - coeffHeckeFun N m ρ (a ∘ₗ a') z
      ∈ coeffCoboundaries ρ := by
    rw [coeffHeckeFun_Ty ρ a a' σ hσ hm ha]
    exact TmS_sub_mem ρ a a' σ hσ hm ha ha' hz
  have h3 := (coeffCoboundaries ρ).sub_mem h2 h1
  rw [coeffHeckeFun_sub] at h3
  convert h3 using 1
  abel

end S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
end P2MW
export P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries (solution)
