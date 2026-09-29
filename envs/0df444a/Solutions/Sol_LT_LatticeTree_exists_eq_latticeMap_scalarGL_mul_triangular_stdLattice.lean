-- Prove2me | solution 1 for LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/da8f563d-28bb-538a-8ca5-eacb320597b1

import Mathlib
import Definitions.Def_LatticeTreeOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice

set_option autoImplicit false

p2m_open "LT.LatticeTree P2MW.S_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice.LT.LatticeTree Matrix"

namespace LT
namespace LatticeTree
p2m_export "LT.LatticeTree" "stdLattice mulVecLinR mulVecLinR_apply latticeMap mem_latticeMap latticeMap_mul latticeMap_inv_latticeMap IsFullLattice scalarGL scalarGL_coe scalarGL_mulVec unitOfNeZero unitOfNeZero_coe"
namespace ApartmentNF
p2m_open "LT.LatticeTree LT"

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem mulVec_tri (a b d : K) (w : Fin 2 → K) :
    (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) K) *ᵥ w = ![a * w 0 + b * w 1, d * w 1] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_scalarGL_le_stdLattice (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    ∃ d : R, ∃ hd : d ≠ 0, latticeMap (scalarGL (unitOfNeZero (K := K) hd)) L ≤ stdLattice R K := by
  classical
  obtain ⟨S, hS⟩ := hL.1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (S ×ˢ (Finset.univ : Finset (Fin 2)))
    (fun p : (Fin 2 → K) × Fin 2 => p.1 p.2)
  have hb0 : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  refine ⟨b, hb0, ?_⟩
  rw [← hS]
  unfold latticeMap
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  intro i
  have := hb (v, i) (Finset.mem_product.mpr ⟨hv, Finset.mem_univ i⟩)
  rw [Algebra.smul_def] at this
  show IsLocalization.IsInteger R ((mulVecLinR (R := R) (scalarGL (unitOfNeZero (K := K) hb0)) v) i)
  rw [mulVecLinR_apply, scalarGL_mulVec, Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]
  exact this

theorem exists_eq_latticeMap_of_le_stdLattice (ϖ : R) (hϖ : Irreducible ϖ)
    (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hle : L ≤ stdLattice R K) :
    ∃ (a b : ℕ) (β' : K) (g' : Matrix.GeneralLinearGroup (Fin 2) K),
      (g' : Matrix (Fin 2) (Fin 2) K) = !![algebraMap R K ϖ ^ a, β'; 0, algebraMap R K ϖ ^ b] ∧
      L = latticeMap g' (stdLattice R K) := by
  classical
  have hϖ0 : algebraMap R K ϖ ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))

  let I₁ : Ideal R :=
    { carrier := {r | ∃ v ∈ L, v 1 = algebraMap R K r}
      add_mem' := by
        rintro r s ⟨v, hv, hvr⟩ ⟨w, hw, hws⟩
        exact ⟨v + w, L.add_mem hv hw, by simp [hvr, hws]⟩
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      smul_mem' := by
        rintro c r ⟨v, hv, hvr⟩
        exact ⟨c • v, L.smul_mem c hv, by simp [hvr, Algebra.smul_def]⟩ }

  let e : R → (Fin 2 → K) := fun r => ![algebraMap R K r, 0]
  have e_add : ∀ r s, e (r + s) = e r + e s := fun r s => by ext i; fin_cases i <;> simp [e]
  have e_smul : ∀ c r, e (c * r) = c • e r := fun c r => by ext i; fin_cases i <;> simp [e, Algebra.smul_def]
  have e_zero : e 0 = 0 := by ext i; fin_cases i <;> simp [e]
  let I₀ : Ideal R :=
    { carrier := {r | e r ∈ L}
      add_mem' := fun {r s} hr hs => by show e (r + s) ∈ L; rw [e_add]; exact L.add_mem hr hs
      zero_mem' := by show e 0 ∈ L; rw [e_zero]; exact L.zero_mem
      smul_mem' := fun c {r} hr => by show e (c * r) ∈ L; rw [e_smul]; exact L.smul_mem c hr }

  have hI₁ : I₁ ≠ ⊥ := by
    intro h
    have hzero : ∀ v ∈ L, v 1 = 0 := by
      intro v hv
      obtain ⟨r, hr⟩ := hle hv 1
      have : r ∈ I₁ := ⟨v, hv, hr.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [← hr, this, map_zero]
    have hsub : Submodule.span K (L : Set (Fin 2 → K)) ≤ LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin 2 => K) 1) := by
      rw [Submodule.span_le]; intro v hv; exact hzero v hv
    have hmem : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ∈ Submodule.span K (L : Set (Fin 2 → K)) := by
      rw [hL.2]; exact Submodule.mem_top
    have := hsub hmem
    simp at this
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI₁ hϖ
  have hwb : ϖ ^ b ∈ I₁ := by rw [hb]; exact Ideal.mem_span_singleton_self _
  obtain ⟨w, hwL, hw1⟩ := hwb
  have hcoord1 : ∀ v ∈ L, ∃ s : R, v 1 = algebraMap R K (ϖ ^ b * s) := by
    intro v hv
    obtain ⟨r, hr⟩ := hle hv 1
    have : r ∈ I₁ := ⟨v, hv, hr.symm⟩
    rw [hb, Ideal.mem_span_singleton] at this
    obtain ⟨s, rfl⟩ := this
    exact ⟨s, hr.symm⟩

  have hdecomp : ∀ v ∈ L, ∃ s t : R, v 1 = algebraMap R K (ϖ ^ b * s) ∧ t ∈ I₀ ∧ v = s • w + e t := by
    intro v hv
    obtain ⟨s, hs⟩ := hcoord1 v hv
    have hu : v - s • w ∈ L := L.sub_mem hv (L.smul_mem s hwL)
    obtain ⟨t, ht⟩ := hle hu 0
    have hu1 : (v - s • w) 1 = 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [Algebra.smul_def, hs, hw1, map_mul, map_pow]; ring
    have ht0 : e t = v - s • w := by
      ext i; fin_cases i
      · simpa [e] using ht
      · simpa [e] using hu1.symm
    refine ⟨s, t, hs, ?_, ?_⟩
    · show e t ∈ L; rw [ht0]; exact hu
    · rw [ht0]; abel

  have hI₀ : I₀ ≠ ⊥ := by
    intro h
    have hline : ∀ v ∈ L, ∃ s : R, v = s • w := by
      intro v hv
      obtain ⟨s, t, -, ht, hv'⟩ := hdecomp v hv
      rw [h, Ideal.mem_bot] at ht
      refine ⟨s, ?_⟩
      rw [hv', ht, e_zero, add_zero]
    have hsub : Submodule.span K (L : Set (Fin 2 → K)) ≤ Submodule.span K {w} := by
      rw [Submodule.span_le]
      intro v hv
      obtain ⟨s, rfl⟩ := hline v hv
      rw [← algebraMap_smul K s w]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    have hw10 : w 1 ≠ 0 := by rw [hw1, map_pow]; exact pow_ne_zero _ hϖ0
    have hmem : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ∈ Submodule.span K {w} := by
      apply hsub; rw [hL.2]; exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := congrFun hk 1
    have h0 := congrFun hk 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      Pi.single_eq_same] at h1 h0
    rcases mul_eq_zero.mp h1 with hk0 | hw0
    · rw [hk0, zero_mul] at h0; exact zero_ne_one h0
    · exact hw10 hw0
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI₀ hϖ
  have hea : e (ϖ ^ a) ∈ L := by show ϖ ^ a ∈ I₀; rw [ha]; exact Ideal.mem_span_singleton_self _

  let A : Matrix (Fin 2) (Fin 2) K := !![algebraMap R K ϖ ^ a, w 0; 0, algebraMap R K ϖ ^ b]
  have hdet : A.det ≠ 0 := by
    simp only [A, Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero (pow_ne_zero _ hϖ0) (pow_ne_zero _ hϖ0)
  refine ⟨a, b, w 0, Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, rfl, ?_⟩
  have hAv : ∀ u : Fin 2 → K, A *ᵥ u = ![algebraMap R K ϖ ^ a * u 0 + w 0 * u 1, algebraMap R K ϖ ^ b * u 1] :=
    fun u => mulVec_tri _ _ _ u
  have hw_eq : w = ![w 0, algebraMap R K (ϖ ^ b)] := by ext i; fin_cases i <;> simp [hw1]
  ext v
  rw [mem_latticeMap]
  constructor
  · intro hv
    obtain ⟨s, t, hs, ht, hv'⟩ := hdecomp v hv
    rw [ha, Ideal.mem_span_singleton] at ht
    obtain ⟨r, rfl⟩ := ht
    refine ⟨![algebraMap R K r, algebraMap R K s], ?_, ?_⟩
    · intro i; fin_cases i; exacts [⟨r, rfl⟩, ⟨s, rfl⟩]
    · show A *ᵥ _ = v
      rw [hAv, hv', hw_eq]
      ext i; fin_cases i <;> simp [e, Algebra.smul_def, map_mul, map_pow] <;> ring
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨r, hr⟩ := hu 0
    obtain ⟨s, hs⟩ := hu 1
    show A *ᵥ u ∈ L
    rw [hAv]
    have : (![algebraMap R K ϖ ^ a * u 0 + w 0 * u 1, algebraMap R K ϖ ^ b * u 1] : Fin 2 → K) = s • w + r • e (ϖ ^ a) := by
      rw [hw_eq]; ext i; fin_cases i <;> simp [e, Algebra.smul_def, ← hr, ← hs, map_pow] <;> ring
    rw [this]
    exact L.add_mem (L.smul_mem s hwL) (L.smul_mem r hea)

end LT.LatticeTree.ApartmentNF

open LT.LatticeTree.ApartmentNF in
theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    ∃ (c : Kˣ) (n : ℤ) (β : K) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = !![algebraMap R K ϖ ^ n, β; 0, 1] ∧
      L = latticeMap (scalarGL c * g) (stdLattice R K) := by
  obtain ⟨d, hd, hle⟩ := exists_scalarGL_le_stdLattice (K := K) L hL
  have hL' : IsFullLattice (latticeMap (scalarGL (unitOfNeZero (K := K) hd)) L) := hL.map _
  obtain ⟨a, b, β', g', hg', hLg'⟩ :=
    exists_eq_latticeMap_of_le_stdLattice ϖ hϖ (latticeMap (scalarGL (unitOfNeZero (K := K) hd)) L) hL' hle
  have hL1 : L = latticeMap ((scalarGL (unitOfNeZero (K := K) hd))⁻¹ * g') (stdLattice R K) := by
    rw [latticeMap_mul, ← hLg', latticeMap_inv_latticeMap]
  have hϖ0 : algebraMap R K ϖ ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))
  set ϖK : K := algebraMap R K ϖ with hϖK
  set c₀ : Kˣ := unitOfNeZero (K := K) hd with hc₀
  let G : Matrix (Fin 2) (Fin 2) K := !![ϖK ^ ((a : ℤ) - b), β' / ϖK ^ b; 0, 1]
  have hG : G.det ≠ 0 := by
    simp only [G, Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
    exact zpow_ne_zero _ hϖ0
  refine ⟨c₀⁻¹ * Units.mk0 (ϖK ^ b) (pow_ne_zero _ hϖ0), (a : ℤ) - b, β' / ϖK ^ b,
    Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, rfl, ?_⟩
  rw [hL1]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg', scalarGL_coe]
  show (((c₀⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * !![algebraMap R K ϖ ^ a, β'; 0, algebraMap R K ϖ ^ b] =
    (((c₀⁻¹ * Units.mk0 (ϖK ^ b) (pow_ne_zero _ hϖ0) : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * G
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, Units.val_mul, Units.val_mk0, ← hϖK]
  have hpow : ϖK ^ b * ϖK ^ ((a : ℤ) - b) = ϖK ^ a := by
    rw [← zpow_natCast, ← zpow_add₀ hϖ0, ← zpow_natCast]; congr 1; ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [G, mul_assoc, hpow]
  · simp [G, mul_div_cancel₀ _ (pow_ne_zero b hϖ0), mul_assoc]
  · simp [G]
  · simp [G]

end S_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
end P2MW
export P2MW.S_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice (solution)
