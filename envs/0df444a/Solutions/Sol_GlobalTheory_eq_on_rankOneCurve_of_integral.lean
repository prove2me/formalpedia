-- Prove2me | solution 1 for GlobalTheory.eq_on_rankOneCurve_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:53:07.513451+00:00
-- url     : https://prove2.me/submissions/a8e70587-4e99-4426-ad6d-c5ea3dfb22e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_eq_of_finite_modular_family
import Theorems.Thm_GlobalTheory_spInvariant_transl
import Theorems.Thm_GlobalTheory_spInvariant_conj
import Theorems.Thm_GlobalTheory_spInvariant_partialInv
import Theorems.Thm_GlobalTheory_rankOneCurve_map_im
import Theorems.Thm_GlobalTheory_rankOneCurve_mem
import Theorems.Thm_GlobalTheory_finite_abs_le_one_mul_mem_range
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_of_symm_mem_phDom
import Theorems.Thm_GlobalTheory_phSym_eq_self_of_isSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eJ_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eJ_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)
include hZs hZe hZ
namespace GlobalTheory
theorem _root_.solution (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {N : ℕ} (hN : N ≠ 0) {R : Matrix (Fin g) (Fin g) ℝ} {u : Fin g → ℝ} (hu : u e = 1)
    (hR : R.IsSymm) (hRe : R e e = 0) (huN : ∀ i, N * u i ∈ (Int.castRingHom ℝ).range)
    (hRN : ∀ i, N * R i e ∈ (Int.castRingHom ℝ).range)
    (hRN2 : ∀ i j, N * N * R i j ∈ (Int.castRingHom ℝ).range) (z w : ℍ) :
    H (rankOneCurve Z R u z) = H (rankOneCurve Z R u w) := by
  set A := (Int.castRingHom ℝ).range with hA
  let ε : Fin g → ℝ := fun i => if i = e then 1 else 0
  have hεe : ε e = 1 := if_pos rfl
  have hε : ∀ i, ε i ∈ A := fun i => by
    by_cases h : i = e <;> simp [ε, h]
  have hNA : (N : ℝ) ∈ A := natCast_mem A N
  let F : Set (ℍ → ℂ) := {f | ∃ (R : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℝ), u e = 1 ∧
    R.IsSymm ∧ R e e = 0 ∧ (∀ i, N * u i ∈ A) ∧ (∀ i, N * R i e ∈ A) ∧
    (∀ i j, N * N * R i j ∈ A) ∧ f = fun z : ℍ => H (rankOneCurve Z R u z)}
  refine eq_of_finite_modular_family (F := F) ?_ ?_ ?_ ?_ ?_
    ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩ z w
  · have hfin := finite_abs_le_one_mul_mem_range (c := (N * N : ℝ)) (by positivity)
    refine (((Set.Finite.pi' fun _ : Fin g => Set.Finite.pi' fun _ : Fin g => hfin).prod
      (Set.Finite.pi' fun _ : Fin g => hfin)).image
        fun p (z : ℍ) => H (rankOneCurve Z (of p.1) p.2 z)).subset ?_
    rintro _ ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩
    let k : Fin g → ℤ := fun i => if i = e then 0 else ⌊u i⌋
    have hke : k e = 0 := if_pos rfl
    have hk : ∀ i, (k i : ℝ) ∈ A := fun i => intCast_mem A _
    let R₁ : Matrix (Fin g) (Fin g) ℝ := of fun i j => R i j - (k i * R j e + R i e * k j)
    have hR₁ : R₁.IsSymm := by
      ext i j
      simp only [R₁, transpose_apply, of_apply, hR.apply i j]
      ring
    refine ⟨(fun i j => Int.fract (R₁ i j), fun i => u i - k i), ⟨fun i j => ⟨?_, ?_⟩,
      fun i => ⟨?_, ?_⟩⟩, funext fun z => ?_⟩
    · exact abs_le.2 ⟨by linarith [Int.fract_nonneg (R₁ i j)], (Int.fract_lt_one _).le⟩
    · have : N * N * Int.fract (R₁ i j) = N * N * R i j - (N * k i * (N * R j e) +
          N * R i e * (N * k j)) - N * N * ⌊R₁ i j⌋ := by
        simp only [Int.fract, R₁, of_apply]
        ring
      simp only [this]
      exact sub_mem (sub_mem (hRN2 i j) (add_mem (mul_mem (mul_mem hNA (hk i)) (hRN j))
        (mul_mem (hRN i) (mul_mem hNA (hk j))))) (mul_mem (mul_mem hNA hNA) (intCast_mem A _))
    · by_cases h : i = e
      · simp [h, hu, hke]
      · simp only [k, if_neg h]
        exact abs_le.2 ⟨by linarith [Int.floor_le (u i)], by linarith [Int.lt_floor_add_one (u i)]⟩
    · simp only [mul_sub, mul_assoc]
      exact sub_mem (mul_mem hNA (huN i)) (mul_mem hNA (mul_mem hNA (hk i)))
    · have h1 := spInvariant_conj hH (rkU (-k) (Pi.single e 1) (by simp [hke]))
        (rankOneCurve_mem hZs hZ hR hu z.im_pos)
      have hfs : (of fun i j => Int.fract (R₁ i j)).IsSymm := by
        ext i j
        simp only [transpose_apply, of_apply, hR₁.apply i j]
      have h2 := spInvariant_transl hH (B := R₁.map Int.floor) (hR₁.map _)
        (rankOneCurve_mem hZs hZ hfs (u := fun i => u i - k i) (by simp [hu, hke]) z.im_pos)
      simp only
      rw [← h1, ← h2]
      congr 1
      ext i j
      have h3 : ((Int.fract (R₁ i j) : ℝ) : ℂ) = R₁ i j - (⌊R₁ i j⌋ : ℤ) := by
        rw [Int.fract]
        push_cast
        rfl
      have hZe' : ∀ i, Z e i = 0 := fun i => (hZs.apply i e).trans (hZe i)
      simp only [rkU_val, mul_apply, map_apply, Matrix.add_apply, transpose_apply, rankOneCurve,
        of_apply, h3]
      simp [one_apply, vecMulVec_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib,
        hZe, hZe', hu, hRe, R₁, hR.apply j e]
      ring
  · rintro _ ⟨R, u, hu, hR, -, -, -, -, rfl⟩
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hd : Differentiable ℂ fun s : ℂ => (of.symm (rankOneCurve Z R u s) : Fin g → Fin g → ℂ) := by
      refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
      simp only [rankOneCurve, of_symm_apply, of_apply]
      fun_prop
    refine (hol.comp hd.differentiableOn fun s (hs : 0 < s.im) =>
      of_symm_mem_phDom (rankOneCurve_mem hZs hZ hR hu hs)).congr fun s hs => ?_
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hs,
      Equiv.apply_symm_apply, phSym_eq_self_of_isSymm (rankOneCurve_mem hZs hZ hR hu hs).1]
  · rintro _ ⟨R, u, hu, hR, -, -, -, -, rfl⟩
    obtain ⟨c, hc, hle⟩ := posDef_exists_mul_dotProduct_le (hZ u hu 1 one_pos)
    obtain ⟨K, hK⟩ := hb c hc
    refine UpperHalfPlane.isBoundedAtImInfty_iff.2 ⟨K, 1, fun z hz =>
      hK _ (rankOneCurve_mem hZs hZ hR hu z.im_pos) ?_⟩
    have h1 : (Z.map Complex.im + (1 : ℝ) • vecMulVec u u -
        c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := by
      refine posSemidef_iff_dotProduct_mulVec.2 ⟨(hZ u hu 1 one_pos).1.sub ?_, fun x => ?_⟩
      · simp [IsHermitian]
      · rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul]
        simpa using hle x
    have h2 := (posSemidef_vecMulVec_self_star u).smul (sub_nonneg.2 hz)
    convert h1.add h2 using 1
    rw [rankOneCurve_map_im]
    simp only [star_trivial, UpperHalfPlane.coe_im]
    module
  · rintro _ ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩
    have hR' : (of fun i j => R i j - u i * (ε j + R j e) - (ε i + R i e) * u j +
        2 * (ε i * ε j)).IsSymm := by
      ext i j
      simp only [transpose_apply, of_apply, hR.apply i j]
      ring
    refine ⟨_, fun i => ε i + R i e, by simp [hεe, hRe], hR', by simp [hεe, hRe, hu]; ring,
      fun i => ?_, fun i => ?_, fun i j => ?_, funext fun z => ?_⟩
    · rw [mul_add]
      exact add_mem (mul_mem hNA (hε i)) (hRN i)
    · convert sub_mem (mul_mem hNA (hε i)) (huN i) using 1
      simp only [of_apply, hεe, hRe, hu]
      ring
    · convert add_mem (sub_mem (sub_mem (hRN2 i j)
        (mul_mem (huN i) (add_mem (mul_mem hNA (hε j)) (hRN j))))
        (mul_mem (add_mem (mul_mem hNA (hε i)) (hRN i)) (huN j)))
        (mul_mem (natCast_mem A 2) (mul_mem (mul_mem hNA (hε i)) (mul_mem hNA (hε j)))) using 1
      simp only [of_apply]
      push_cast
      ring
    · symm
      refine spInvariant_partialInv hH e
        (rankOneCurve_mem hZs hZ hR hu (ModularGroup.S • z).im_pos) fun i k => ?_
      have hZe' : ∀ i, Z e i = 0 := fun i => (hZs.apply i e).trans (hZe i)
      have hz := z.ne_zero
      simp only [rankOneCurve, of_apply, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
        hZe, hZe', hεe, hu, hRe, hR.apply k e]
      by_cases hi : i = e <;> by_cases hk : k = e <;>
        simp [ε, hi, hk, eq_comm (a := e), hZe, hZe', hu, hRe, hR.apply k e] <;>
        field_simp <;> ring
  · rintro _ ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩
    have hR' : (of fun i j => R i j + u i * u j - ε i * ε j).IsSymm := by
      ext i j
      simp only [transpose_apply, of_apply, hR.apply i j]
      ring
    refine ⟨_, u, hu, hR', by simp [hεe, hRe, hu], huN, fun i => ?_, fun i j => ?_,
      funext fun z => ?_⟩
    · convert sub_mem (add_mem (hRN i) (huN i)) (mul_mem hNA (hε i)) using 1
      simp only [of_apply, hεe, hu]
      ring
    · convert sub_mem (add_mem (hRN2 i j) (mul_mem (huN i) (huN j)))
        (mul_mem (mul_mem hNA (hε i)) (mul_mem hNA (hε j))) using 1
      simp only [of_apply]
      ring
    · rw [← spInvariant_transl hH (eJ_symm e) (rankOneCurve_mem hZs hZ hR' hu z.im_pos)]
      refine congrArg H ?_
      ext i j
      simp only [rankOneCurve, of_apply, UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd,
        Matrix.add_apply, map_apply, eJ_apply]
      by_cases hi : i = e <;> by_cases hj : j = e <;> simp [ε, hi, hj, eq_comm (a := e)] <;> ring
end GlobalTheory
