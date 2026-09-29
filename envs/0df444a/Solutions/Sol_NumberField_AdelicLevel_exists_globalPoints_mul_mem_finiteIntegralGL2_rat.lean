-- Prove2me | solution 1 for NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/76b7faa3-e928-5e28-a0e0-2bf01a5d3fa0

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField AutomorphicForm"

noncomputable section

namespace NumberField
p2m_export "NumberField" "place RingOfIntegers classNumber_eq_one_iff AdelicLevel.glFin AdelicLevel.finiteIntegralGL2 AdelicBox.algebraMap_mem_adicCompletionIntegers AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles"
namespace AdelicLevel
p2m_export "NumberField.AdelicLevel" "algebraMap_mem_adicCompletionIntegers glFin coe_zero_apply coe_one_apply coe_add_apply coe_mul_apply coe_sub_apply coe_neg_apply finiteIntegralGL2 mem_finiteIntegralGL2_iff"
namespace GL2StrongApproxW8M
p2m_open "NumberField.AdelicLevel NumberField"

section ElementaryMatrices

variable {S : Type*} [CommRing S]

def lowerUnipGL2 (x : S) : GL (Fin 2) S where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem lowerUnipGL2_coe (x : S) :
    (lowerUnipGL2 x : Matrix (Fin 2) (Fin 2) S) = !![1, 0; x, 1] := rfl

theorem lowerUnipGL2_inv (x : S) : (lowerUnipGL2 x)⁻¹ = lowerUnipGL2 (-x) :=
  Units.ext rfl

theorem unipotentGL2_inv (x : S) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  Units.ext rfl

theorem lowerUnipGL2_add (x y : S) :
    lowerUnipGL2 (x + y) = lowerUnipGL2 x * lowerUnipGL2 y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]

theorem map_lowerUnipGL2 {T : Type*} [CommRing T] (f : S →+* T) (x : S) :
    GeneralLinearGroup.map f (lowerUnipGL2 x) = lowerUnipGL2 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipGL2, GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem map_unipotentGL2 {T : Type*} [CommRing T] (f : S →+* T) (x : S) :
    GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentGL2, GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]

def diagTorusGL2 (u : Sˣ) : GL (Fin 2) S where
  val := !![1, 0; 0, (u : S)]
  inv := !![1, 0; 0, ((u⁻¹ : Sˣ) : S)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diagTorusGL2_coe (u : Sˣ) :
    (diagTorusGL2 u : Matrix (Fin 2) (Fin 2) S) = !![1, 0; 0, (u : S)] := rfl

theorem diagTorusGL2_mul (u w : Sˣ) :
    diagTorusGL2 (u * w) = diagTorusGL2 u * diagTorusGL2 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]

theorem map_diagTorusGL2 {T : Type*} [CommRing T] (f : S →+* T) (u : Sˣ) :
    GeneralLinearGroup.map f (diagTorusGL2 u) = diagTorusGL2 (Units.map (f : S →* T) u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagTorusGL2, GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem conj_unipotent_entry {u w : Matrix (Fin 2) (Fin 2) S} (h : u * w = 1) (b : S)
    (i j : Fin 2) :
    (u * !![1, b; 0, 1] * w) i j
      = (1 : Matrix (Fin 2) (Fin 2) S) i j + b * (u i 0 * w 1 j) := by
  have hcalc : (u * !![1, b; 0, 1] * w) i j = (u * w) i j + b * (u i 0 * w 1 j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hcalc, h]

theorem conj_lowerUnip_entry {u w : Matrix (Fin 2) (Fin 2) S} (h : u * w = 1) (b : S)
    (i j : Fin 2) :
    (u * !![1, 0; b, 1] * w) i j
      = (1 : Matrix (Fin 2) (Fin 2) S) i j + b * (u i 1 * w 0 j) := by
  have hcalc : (u * !![1, 0; b, 1] * w) i j = (u * w) i j + b * (u i 1 * w 0 j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hcalc, h]

theorem gauss_factorization (M : Matrix (Fin 2) (Fin 2) S) (c ci δ δi : S)
    (hc : M 1 0 = c) (hci : c * ci = 1) (hδ : M.det = δ) (hδi : δ * δi = 1) :
    !![1, (M 0 0 - 1) * ci; 0, 1] * !![1, 0; c, 1]
        * !![1, (M 1 1 * δi - 1) * ci; 0, 1]
        * !![1, 0; 0, δ] = M := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = δ := by
    rw [← Matrix.det_fin_two]; exact hδ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (M 0 0 - 1) * hci
  · linear_combination
      (M 0 1 + (M 0 0 - 1) * (M 1 1 * δi - 1) * ci * δ) * hci
        + (ci * M 0 1) * hc + ci * hdet + (ci * M 0 0 * M 1 1) * hδi
  · linear_combination - hc
  · linear_combination ((M 1 1 * δi - 1) * δ) * hci + M 1 1 * hδi

end ElementaryMatrices

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem algebraMap_finiteAdeleRing_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K (FiniteAdeleRing R K) x) v = algebraMap K (v.adicCompletion K) x := rfl

theorem valued_algebraMap_finiteAdeleRing_apply (k : K) (v : HeightOneSpectrum R) :
    Valued.v ((algebraMap K (FiniteAdeleRing R K) k) v) = v.valuation K k := by
  rw [show (algebraMap K (FiniteAdeleRing R K) k) v = ((k : K) : v.adicCompletion K) from rfl]
  exact valuedAdicCompletion_eq_valuation' v k

theorem one_apply_mem (v : HeightOneSpectrum R) :
    (1 : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K := by
  rw [coe_one_apply]; exact one_mem _

theorem zero_apply_mem (v : HeightOneSpectrum R) :
    (0 : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K := by
  rw [coe_zero_apply]; exact zero_mem _

theorem one_matrix_apply_mem (i j : Fin 2) (v : HeightOneSpectrum R) :
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v ∈ v.adicCompletionIntegers K := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq]
    exact one_apply_mem R K v
  · rw [Matrix.one_apply_ne h]
    exact zero_apply_mem R K v

theorem unipotentGL2_mem {a : FiniteAdeleRing R K}
    (ha : ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K) :
    unipotentGL2 a ∈ finiteIntegralGL2 R K := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact ha v
    · exact zero_apply_mem R K v
    · exact one_apply_mem R K v
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · show (-a) v ∈ v.adicCompletionIntegers K
      rw [coe_neg_apply]
      exact neg_mem (ha v)
    · exact zero_apply_mem R K v
    · exact one_apply_mem R K v

theorem lowerUnipGL2_mem {a : FiniteAdeleRing R K}
    (ha : ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K) :
    lowerUnipGL2 a ∈ finiteIntegralGL2 R K := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact ha v
    · exact one_apply_mem R K v
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · show (-a) v ∈ v.adicCompletionIntegers K
      rw [coe_neg_apply]
      exact neg_mem (ha v)
    · exact one_apply_mem R K v

theorem diagTorusGL2_mem {u : (FiniteAdeleRing R K)ˣ}
    (hu : ∀ v : HeightOneSpectrum R, (u : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K)
    (hu' : ∀ v : HeightOneSpectrum R,
      ((u⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) :
    diagTorusGL2 u ∈ finiteIntegralGL2 R K := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact hu v
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact hu' v

theorem exists_sub_algebraMap_eq_mul_integral (a : FiniteAdeleRing R K) (d : K)
    (hd : d ≠ 0) :
    ∃ q : K, ∀ v : HeightOneSpectrum R,
      ∃ c ∈ v.adicCompletionIntegers K,
        a v - algebraMap K (v.adicCompletion K) q
          = algebraMap K (v.adicCompletion K) d * c := by
  have hdu : IsUnit (algebraMap K (FiniteAdeleRing R K) d) :=
    (Ne.isUnit hd).map (algebraMap K (FiniteAdeleRing R K))
  set a' : FiniteAdeleRing R K := ↑hdu.unit⁻¹ * a with ha'
  obtain ⟨k, hk⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles R K a'
  have hk' : ∀ v : HeightOneSpectrum R,
      (algebraMap K (FiniteAdeleRing R K) k + a') v ∈ v.adicCompletionIntegers K := hk
  refine ⟨d * (-k), fun v ↦ ⟨a' v - algebraMap K (v.adicCompletion K) (-k), ?_, ?_⟩⟩
  · have hkv : algebraMap K (v.adicCompletion K) k + a' v ∈ v.adicCompletionIntegers K := hk' v
    rw [map_neg, sub_neg_eq_add, add_comm]
    exact hkv
  have hda' : algebraMap K (FiniteAdeleRing R K) d * a' = a := by
    have h1 : algebraMap K (FiniteAdeleRing R K) d * ↑hdu.unit⁻¹ = 1 := by
      have h2 := hdu.unit.mul_inv
      rwa [hdu.unit_spec] at h2
    rw [ha', ← mul_assoc, h1, one_mul]
  calc a v - algebraMap K (v.adicCompletion K) (d * -k)
      = (algebraMap K (FiniteAdeleRing R K) d * a') v
          - algebraMap K (v.adicCompletion K) d * algebraMap K (v.adicCompletion K) (-k) := by
        rw [hda', map_mul]
    _ = algebraMap K (v.adicCompletion K) d * a' v
          - algebraMap K (v.adicCompletion K) d * algebraMap K (v.adicCompletion K) (-k) := by
        rw [coe_mul_apply, algebraMap_finiteAdeleRing_apply]
    _ = algebraMap K (v.adicCompletion K) d
          * (a' v - algebraMap K (v.adicCompletion K) (-k)) := by ring

theorem exists_common_denominator (γ : GL (Fin 2) K) :
    ∃ d : R, d ≠ 0 ∧ ∀ i j k l : Fin 2,
      ∃ n : R, algebraMap R K d
          * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            * ((γ : Matrix (Fin 2) (Fin 2) K) k l))
        = algebraMap R K n := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset (Fin 2 × Fin 2 × Bool))
    (fun p ↦ if p.2.2 then ((γ : Matrix (Fin 2) (Fin 2) K) p.1 p.2.1)
      else (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) p.1 p.2.1))
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  refine ⟨b * b, mul_ne_zero hb0 hb0, fun i j k l ↦ ?_⟩
  obtain ⟨n₁, hn₁⟩ := hb (i, j, false) (Finset.mem_univ _)
  obtain ⟨n₂, hn₂⟩ := hb (k, l, true) (Finset.mem_univ _)
  refine ⟨n₁ * n₂, ?_⟩
  have h₁ : algebraMap R K n₁
      = algebraMap R K b * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
    simpa [Algebra.smul_def] using hn₁
  have h₂ : algebraMap R K n₂
      = algebraMap R K b * ((γ : Matrix (Fin 2) (Fin 2) K) k l) := by
    simpa [Algebra.smul_def] using hn₂
  rw [map_mul, map_mul, h₁, h₂]
  ring

abbrev ratGL (γ : GL (Fin 2) K) : GL (Fin 2) (FiniteAdeleRing R K) :=
  GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ

theorem ratGL_mul (γ γ' : GL (Fin 2) K) : ratGL R K (γ * γ') = ratGL R K γ * ratGL R K γ' :=
  map_mul _ _ _

theorem ratGL_inv_mul_val (γ : GL (Fin 2) K) :
    (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem ratGL_val_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = algebraMap K (FiniteAdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) :=
  GeneralLinearGroup.map_apply (algebraMap K (FiniteAdeleRing R K)) i j γ

theorem ratGL_inv_val_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = algebraMap K (FiniteAdeleRing R K)
          (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
  rw [show (ratGL R K γ)⁻¹ = ratGL R K γ⁻¹ from
    (map_inv (GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K))) γ).symm]
  exact GeneralLinearGroup.map_apply (algebraMap K (FiniteAdeleRing R K)) i j γ⁻¹

theorem conj_entry_mem (γ : GL (Fin 2) K) (d : R)
    (hd : ∀ i j k l : Fin 2, ∃ n : R, algebraMap R K d
          * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            * ((γ : Matrix (Fin 2) (Fin 2) K) k l)) = algebraMap R K n)
    (b : FiniteAdeleRing R K)
    (hb : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
        b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c)
    (x : FiniteAdeleRing R K) (hx : x = b ∨ x = -b) (i p q j : Fin 2)
    (v : HeightOneSpectrum R) :
    ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      + x * ((((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i p
             * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) q j)) v
      ∈ v.adicCompletionIntegers K := by
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply]
  refine add_mem (one_matrix_apply_mem R K i j v) ?_
  rw [ratGL_inv_val_apply, ratGL_val_apply, algebraMap_finiteAdeleRing_apply,
    algebraMap_finiteAdeleRing_apply, ← map_mul]
  obtain ⟨c, hcmem, hc⟩ := hb v
  obtain ⟨n, hn⟩ := hd i p q j
  have hkey : algebraMap K (v.adicCompletion K) (algebraMap R K d)
      * algebraMap K (v.adicCompletion K)
          ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
            * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))
      = algebraMap K (v.adicCompletion K) (algebraMap R K n) := by
    rw [← map_mul, hn]
  have hint : c * algebraMap K (v.adicCompletion K) (algebraMap R K n)
      ∈ v.adicCompletionIntegers K :=
    mul_mem hcmem (NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers R K v n)
  have hxv : x v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c
      ∨ x v = -(algebraMap K (v.adicCompletion K) (algebraMap R K d) * c) := by
    rcases hx with hx | hx
    · exact Or.inl (by rw [hx, hc])
    · exact Or.inr (by rw [hx, coe_neg_apply, hc])
  rcases hxv with hxv | hxv
  · rw [hxv, show algebraMap K (v.adicCompletion K) (algebraMap R K d) * c
        * algebraMap K (v.adicCompletion K)
          ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
            * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))
        = c * (algebraMap K (v.adicCompletion K) (algebraMap R K d)
          * algebraMap K (v.adicCompletion K)
            ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
              * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))) from by ring, hkey]
    exact hint
  · rw [hxv, show -(algebraMap K (v.adicCompletion K) (algebraMap R K d) * c)
        * algebraMap K (v.adicCompletion K)
          ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
            * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))
        = -(c * (algebraMap K (v.adicCompletion K) (algebraMap R K d)
          * algebraMap K (v.adicCompletion K)
            ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
              * ((γ : Matrix (Fin 2) (Fin 2) K) q j))))) from by ring, hkey]
    exact neg_mem hint

theorem exists_conj_unipotent_mem (γ : GL (Fin 2) K) (a : FiniteAdeleRing R K) :
    ∃ q : K,
      (ratGL R K γ)⁻¹ * unipotentGL2 (a - algebraMap K (FiniteAdeleRing R K) q) * ratGL R K γ
        ∈ finiteIntegralGL2 R K := by
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator R K γ
  have hdK : algebraMap R K d ≠ 0 := fun hcontra ↦
    hd0 (IsFractionRing.injective R K (by rw [hcontra, map_zero]))
  obtain ⟨q, hq⟩ := exists_sub_algebraMap_eq_mul_integral R K a (algebraMap R K d) hdK
  refine ⟨q, ?_⟩
  set b : FiniteAdeleRing R K := a - algebraMap K (FiniteAdeleRing R K) q with hb
  have hbv : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
      b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c := by
    intro v
    obtain ⟨c, hcmem, hc⟩ := hq v
    refine ⟨c, hcmem, ?_⟩
    rw [hb, coe_sub_apply, algebraMap_finiteAdeleRing_apply]
    exact hc
  have hAB := ratGL_inv_mul_val R K γ
  have hval : ((((ratGL R K γ)⁻¹ * unipotentGL2 b * ratGL R K γ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, b; 0, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [Units.val_mul, Units.val_mul, unipotentGL2_coe]
  have hinvval : ((((ratGL R K γ)⁻¹ * unipotentGL2 b * ratGL R K γ)⁻¹ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, -b; 0, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, unipotentGL2_inv, ← mul_assoc,
      Units.val_mul, Units.val_mul, unipotentGL2_coe]
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    rw [hval, conj_unipotent_entry hAB b i j]
    exact conj_entry_mem R K γ d hd b hbv b (Or.inl rfl) i 0 1 j v
  · intro i j v
    rw [hinvval, conj_unipotent_entry hAB (-b) i j]
    exact conj_entry_mem R K γ d hd b hbv (-b) (Or.inr rfl) i 0 1 j v

theorem exists_conj_lowerUnip_mem (γ : GL (Fin 2) K) (a : FiniteAdeleRing R K) :
    ∃ q : K,
      (ratGL R K γ)⁻¹ * lowerUnipGL2 (a - algebraMap K (FiniteAdeleRing R K) q) * ratGL R K γ
        ∈ finiteIntegralGL2 R K := by
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator R K γ
  have hdK : algebraMap R K d ≠ 0 := fun hcontra ↦
    hd0 (IsFractionRing.injective R K (by rw [hcontra, map_zero]))
  obtain ⟨q, hq⟩ := exists_sub_algebraMap_eq_mul_integral R K a (algebraMap R K d) hdK
  refine ⟨q, ?_⟩
  set b : FiniteAdeleRing R K := a - algebraMap K (FiniteAdeleRing R K) q with hb
  have hbv : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
      b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c := by
    intro v
    obtain ⟨c, hcmem, hc⟩ := hq v
    refine ⟨c, hcmem, ?_⟩
    rw [hb, coe_sub_apply, algebraMap_finiteAdeleRing_apply]
    exact hc
  have hAB := ratGL_inv_mul_val R K γ
  have hval : ((((ratGL R K γ)⁻¹ * lowerUnipGL2 b * ratGL R K γ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, 0; b, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [Units.val_mul, Units.val_mul, lowerUnipGL2_coe]
  have hinvval : ((((ratGL R K γ)⁻¹ * lowerUnipGL2 b * ratGL R K γ)⁻¹ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, 0; -b, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, lowerUnipGL2_inv, ← mul_assoc,
      Units.val_mul, Units.val_mul, lowerUnipGL2_coe]
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    rw [hval, conj_lowerUnip_entry hAB b i j]
    exact conj_entry_mem R K γ d hd b hbv b (Or.inl rfl) i 1 0 j v
  · intro i j v
    rw [hinvval, conj_lowerUnip_entry hAB (-b) i j]
    exact conj_entry_mem R K γ d hd b hbv (-b) (Or.inr rfl) i 1 0 j v

theorem absorb_unipotent_left {X : GL (Fin 2) (FiniteAdeleRing R K)} {γ : GL (Fin 2) K}
    (hX : (ratGL R K γ)⁻¹ * X ∈ finiteIntegralGL2 R K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K (unipotentGL2 q * γ))⁻¹ * (unipotentGL2 a * X)
      ∈ finiteIntegralGL2 R K := by
  obtain ⟨q, hq⟩ := exists_conj_unipotent_mem R K γ a
  refine ⟨q, ?_⟩
  have hsplit : unipotentGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
      = (unipotentGL2 (algebraMap K (FiniteAdeleRing R K) q))⁻¹ * unipotentGL2 a := by
    rw [eq_inv_mul_iff_mul_eq, ← unipotentGL2_add]
    congr 1
    ring
  have key : (ratGL R K (unipotentGL2 q * γ))⁻¹ * (unipotentGL2 a * X)
      = ((ratGL R K γ)⁻¹ * unipotentGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
          * ratGL R K γ) * ((ratGL R K γ)⁻¹ * X) := by
    rw [ratGL_mul, show ratGL R K (unipotentGL2 q)
        = unipotentGL2 (algebraMap K (FiniteAdeleRing R K) q) from map_unipotentGL2 _ _, hsplit]
    group
  rw [key]
  exact mul_mem hq hX

theorem absorb_lowerUnip_left {X : GL (Fin 2) (FiniteAdeleRing R K)} {γ : GL (Fin 2) K}
    (hX : (ratGL R K γ)⁻¹ * X ∈ finiteIntegralGL2 R K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K (lowerUnipGL2 q * γ))⁻¹ * (lowerUnipGL2 a * X)
      ∈ finiteIntegralGL2 R K := by
  obtain ⟨q, hq⟩ := exists_conj_lowerUnip_mem R K γ a
  refine ⟨q, ?_⟩
  have hsplit : lowerUnipGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
      = (lowerUnipGL2 (algebraMap K (FiniteAdeleRing R K) q))⁻¹ * lowerUnipGL2 a := by
    rw [eq_inv_mul_iff_mul_eq, ← lowerUnipGL2_add]
    congr 1
    ring
  have key : (ratGL R K (lowerUnipGL2 q * γ))⁻¹ * (lowerUnipGL2 a * X)
      = ((ratGL R K γ)⁻¹ * lowerUnipGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
          * ratGL R K γ) * ((ratGL R K γ)⁻¹ * X) := by
    rw [ratGL_mul, show ratGL R K (lowerUnipGL2 q)
        = lowerUnipGL2 (algebraMap K (FiniteAdeleRing R K) q) from map_lowerUnipGL2 _ _, hsplit]
    group
  rw [key]
  exact mul_mem hq hX

theorem mul_lowerUnip_apply_one_zero (g : GL (Fin 2) (FiniteAdeleRing R K))
    (t : FiniteAdeleRing R K) :
    ((g * lowerUnipGL2 t : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
      = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
        + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t := by
  rw [Units.val_mul, lowerUnipGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_apply (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) (v : HeightOneSpectrum R) :
    M.det v = M 0 0 v * M 1 1 v - M 0 1 v * M 1 0 v := by
  rw [Matrix.det_fin_two]; rfl

theorem exists_lowerUnip_translate_isUnit (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ t : FiniteAdeleRing R K, (∀ v : HeightOneSpectrum R, t v ∈ v.adicCompletionIntegers K) ∧
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
        + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t) := by
  classical
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hM
  set N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hN

  have hMN : M.det * N.det = 1 := by
    rw [← Matrix.det_mul, hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdetprod : ∀ v : HeightOneSpectrum R, M.det v * N.det v = 1 := by
    intro v
    rw [← coe_mul_apply, hMN]; rfl
  have hdet_ne : ∀ v : HeightOneSpectrum R, M.det v ≠ 0 := by
    intro v hzero
    have h1 := hdetprod v
    rw [hzero, zero_mul] at h1
    exact zero_ne_one h1

  have hrow : ∀ v : HeightOneSpectrum R, ¬(M 1 0 v = 0 ∧ M 1 1 v = 0) := by
    intro v ⟨h0, h1⟩
    apply hdet_ne v
    rw [det_apply R K M v, h0, h1, mul_zero, mul_zero, sub_zero]

  set tfun : (v : HeightOneSpectrum R) → v.adicCompletion K := fun v ↦
    if Valued.v (M 1 0 v) < Valued.v (M 1 1 v) then 1 else 0 with htfun
  have htfun_eval : ∀ v : HeightOneSpectrum R, tfun v
      = if Valued.v (M 1 0 v) < Valued.v (M 1 1 v) then (1 : v.adicCompletion K) else 0 :=
    fun v ↦ rfl
  have htint : ∀ v, tfun v ∈ v.adicCompletionIntegers K := by
    intro v
    rw [htfun_eval v]
    split
    · exact one_mem _
    · exact zero_mem _
  set t : FiniteAdeleRing R K :=
    ⟨tfun, Filter.Eventually.of_forall fun v ↦ htint v⟩ with ht
  have htv : ∀ v, t v = tfun v := fun v ↦ rfl
  refine ⟨t, fun v ↦ by rw [htv v]; exact htint v, ?_⟩

  set c : FiniteAdeleRing R K := M 1 0 + M 1 1 * t with hc
  have hcv : ∀ v, c v = M 1 0 v + M 1 1 v * tfun v := fun v ↦ rfl

  have hcne : ∀ v, c v ≠ 0 := by
    intro v
    rw [hcv v, htfun_eval v]
    split
    · rename_i hlt
      intro hzero
      have hne : Valued.v (M 1 0 v) ≠ Valued.v (M 1 1 v) := ne_of_lt hlt
      have hval : Valued.v (M 1 0 v + M 1 1 v) =
          max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) :=
        Valuation.map_add_of_distinct_val _ hne
      rw [mul_one] at hzero
      rw [hzero, Valuation.map_zero, max_eq_right (le_of_lt hlt)] at hval
      have hd0 : M 1 1 v = 0 := by
        have := hval.symm
        rwa [Valuation.zero_iff] at this
      have hc0 : M 1 0 v = 0 := by
        have := hzero
        rwa [hd0, add_zero] at this
      exact hrow v ⟨hc0, hd0⟩
    · rename_i hge
      rw [mul_zero, add_zero]
      intro hzero
      have hc0 : Valued.v (M 1 0 v) = 0 := by rw [hzero, Valuation.map_zero]
      have hd0 : Valued.v (M 1 1 v) = 0 := by
        have hle : Valued.v (M 1 1 v) ≤ Valued.v (M 1 0 v) := not_lt.mp hge
        rw [hc0] at hle
        exact le_zero_iff.mp hle
      rw [Valuation.zero_iff] at hd0
      exact hrow v ⟨hzero, hd0⟩

  have hcunit : ∀ᶠ v in Filter.cofinite, Valued.v (c v) = 1 := by
    have h00 : ∀ᶠ v in Filter.cofinite, M 0 0 v ∈ v.adicCompletionIntegers K := (M 0 0).2
    have h01 : ∀ᶠ v in Filter.cofinite, M 0 1 v ∈ v.adicCompletionIntegers K := (M 0 1).2
    have h10 : ∀ᶠ v in Filter.cofinite, M 1 0 v ∈ v.adicCompletionIntegers K := (M 1 0).2
    have h11 : ∀ᶠ v in Filter.cofinite, M 1 1 v ∈ v.adicCompletionIntegers K := (M 1 1).2
    have k00 : ∀ᶠ v in Filter.cofinite, N 0 0 v ∈ v.adicCompletionIntegers K := (N 0 0).2
    have k01 : ∀ᶠ v in Filter.cofinite, N 0 1 v ∈ v.adicCompletionIntegers K := (N 0 1).2
    have k10 : ∀ᶠ v in Filter.cofinite, N 1 0 v ∈ v.adicCompletionIntegers K := (N 1 0).2
    have k11 : ∀ᶠ v in Filter.cofinite, N 1 1 v ∈ v.adicCompletionIntegers K := (N 1 1).2
    filter_upwards [h00, h01, h10, h11, k00, k01, k10, k11] with v
      h00 h01 h10 h11 k00 k01 k10 k11
    have hMdetint : M.det v ∈ v.adicCompletionIntegers K := by
      rw [det_apply R K M v]
      exact sub_mem (mul_mem h00 h11) (mul_mem h01 h10)
    have hNdetint : N.det v ∈ v.adicCompletionIntegers K := by
      rw [det_apply R K N v]
      exact sub_mem (mul_mem k00 k11) (mul_mem k01 k10)
    have hdetone : Valued.v (M.det v) = 1 := by
      have hprodval : Valued.v (M.det v) * Valued.v (N.det v) = 1 := by
        rw [← Valuation.map_mul, hdetprod v, Valuation.map_one]
      have hMle : Valued.v (M.det v) ≤ 1 := by
        rwa [← mem_adicCompletionIntegers]
      have hNle : Valued.v (N.det v) ≤ 1 := by
        rwa [← mem_adicCompletionIntegers]
      have hge : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v (M.det v) := by
        calc (1 : WithZero (Multiplicative ℤ))
            = Valued.v (M.det v) * Valued.v (N.det v) := hprodval.symm
          _ ≤ Valued.v (M.det v) * 1 := mul_le_mul' le_rfl hNle
          _ = Valued.v (M.det v) := mul_one _
      exact le_antisymm hMle hge

    have hmax : (1 : WithZero (Multiplicative ℤ))
        ≤ max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) := by
      have hsub : Valued.v (M.det v)
          ≤ max (Valued.v (M 0 0 v * M 1 1 v)) (Valued.v (M 0 1 v * M 1 0 v)) := by
        rw [det_apply R K M v]
        exact Valuation.map_sub _ _ _
      have h1 : Valued.v (M 0 0 v * M 1 1 v) ≤ Valued.v (M 1 1 v) := by
        rw [Valuation.map_mul]
        calc Valued.v (M 0 0 v) * Valued.v (M 1 1 v) ≤ 1 * Valued.v (M 1 1 v) :=
              mul_le_mul' (by rwa [← mem_adicCompletionIntegers]) le_rfl
          _ = Valued.v (M 1 1 v) := one_mul _
      have h2 : Valued.v (M 0 1 v * M 1 0 v) ≤ Valued.v (M 1 0 v) := by
        rw [Valuation.map_mul]
        calc Valued.v (M 0 1 v) * Valued.v (M 1 0 v) ≤ 1 * Valued.v (M 1 0 v) :=
              mul_le_mul' (by rwa [← mem_adicCompletionIntegers]) le_rfl
          _ = Valued.v (M 1 0 v) := one_mul _
      calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (M.det v) := hdetone.symm
        _ ≤ max (Valued.v (M 0 0 v * M 1 1 v)) (Valued.v (M 0 1 v * M 1 0 v)) := hsub
        _ ≤ max (Valued.v (M 1 1 v)) (Valued.v (M 1 0 v)) := max_le_max h1 h2
        _ = max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) := max_comm _ _
    rw [hcv v, htfun_eval v]
    split
    · rename_i hlt
      rw [mul_one]
      have hne : Valued.v (M 1 0 v) ≠ Valued.v (M 1 1 v) := ne_of_lt hlt
      rw [Valuation.map_add_of_distinct_val _ hne]
      have hmaxeq : max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) = Valued.v (M 1 1 v) :=
        max_eq_right (le_of_lt hlt)
      rw [hmaxeq]
      refine le_antisymm (by rwa [← mem_adicCompletionIntegers]) ?_
      rw [hmaxeq] at hmax
      exact hmax
    · rename_i hge
      rw [mul_zero, add_zero]
      have hmaxeq : max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) = Valued.v (M 1 0 v) :=
        max_eq_left (not_lt.mp hge)
      refine le_antisymm (by rwa [← mem_adicCompletionIntegers]) ?_
      rw [hmaxeq] at hmax
      exact hmax

  set cinvfun : (v : HeightOneSpectrum R) → v.adicCompletion K := fun v ↦ (c v)⁻¹
    with hcinvfun
  have hcinv_ev : ∀ᶠ v in Filter.cofinite,
      cinvfun v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    filter_upwards [hcunit] with v hv
    show (c v)⁻¹ ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    rw [SetLike.mem_coe, mem_adicCompletionIntegers, Valuation.map_inv, hv]
    exact le_of_eq inv_one
  set cinv : FiniteAdeleRing R K := ⟨cinvfun, hcinv_ev⟩ with hcinv
  have hcinvv : ∀ v, cinv v = (c v)⁻¹ := fun v ↦ rfl
  have hmul : c * cinv = 1 := by
    have hkey : ∀ w : HeightOneSpectrum R, (c * cinv) w = (1 : FiniteAdeleRing R K) w := by
      intro w
      rw [coe_mul_apply, hcinvv w, mul_inv_cancel₀ (hcne w), coe_one_apply]
    exact Subtype.ext (funext fun w ↦ hkey w)
  exact ⟨⟨c, cinv, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

def detUnit (g : GL (Fin 2) (FiniteAdeleRing R K)) : (FiniteAdeleRing R K)ˣ where
  val := ((g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det
  inv := ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det
  val_inv := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  inv_val := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

@[scoped simp] theorem detUnit_coe (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    (detUnit R K g : FiniteAdeleRing R K)
      = ((g : GL (Fin 2) (FiniteAdeleRing R K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det := rfl

theorem exists_gauss_decomposition (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ (t : FiniteAdeleRing R K) (x z : FiniteAdeleRing R K) (cu : (FiniteAdeleRing R K)ˣ),
      (∀ v : HeightOneSpectrum R, t v ∈ v.adicCompletionIntegers K) ∧
      g = unipotentGL2 x * (lowerUnipGL2 (cu : FiniteAdeleRing R K)
        * (unipotentGL2 z * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t)))) := by
  obtain ⟨t, htint, hunit⟩ := exists_lowerUnip_translate_isUnit R K g
  set h : GL (Fin 2) (FiniteAdeleRing R K) := g * lowerUnipGL2 t with hh
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    (h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hM
  have hM10 : M 1 0 = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
      + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t := by
    rw [hM, hh, mul_lowerUnip_apply_one_zero]
  set cu : (FiniteAdeleRing R K)ˣ := hunit.unit with hcu
  have hcuval : (cu : FiniteAdeleRing R K)
      = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
        + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t := hunit.unit_spec
  have hc : M 1 0 = (cu : FiniteAdeleRing R K) := by rw [hM10, hcuval]
  have hdet : M.det = (detUnit R K g : FiniteAdeleRing R K) := by
    rw [hM, hh, Units.val_mul, Matrix.det_mul, lowerUnipGL2_coe, Matrix.det_fin_two_of]
    rw [detUnit_coe]
    ring
  have hfact := gauss_factorization M (cu : FiniteAdeleRing R K)
    ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
    (detUnit R K g : FiniteAdeleRing R K)
    (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
    hc cu.mul_inv hdet (detUnit R K g).mul_inv
  set x : FiniteAdeleRing R K :=
    (M 0 0 - 1) * ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) with hx
  set z : FiniteAdeleRing R K :=
    (M 1 1 * (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) - 1)
      * ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) with hz
  have hgroup : unipotentGL2 x * lowerUnipGL2 (cu : FiniteAdeleRing R K)
      * unipotentGL2 z * diagTorusGL2 (detUnit R K g) = h := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, unipotentGL2_coe, lowerUnipGL2_coe,
      unipotentGL2_coe, diagTorusGL2_coe]
    rw [hx, hz]
    exact hfact
  refine ⟨t, x, z, cu, htint, ?_⟩
  have hgh : g = h * (lowerUnipGL2 t)⁻¹ := by
    rw [hh, mul_assoc, mul_inv_cancel, mul_one]
  have hassoc : unipotentGL2 x * (lowerUnipGL2 (cu : FiniteAdeleRing R K)
      * (unipotentGL2 z * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t))))
      = h * (lowerUnipGL2 t)⁻¹ := by
    rw [← hgroup, lowerUnipGL2_inv]
    group
  rw [hassoc]
  exact hgh

omit [IsFractionRing R K] in

theorem exists_primeGenerator [IsPrincipalIdealRing R] (v : HeightOneSpectrum R) :
    ∃ π : R, π ≠ 0 ∧ v.intValuation π = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum R, w ≠ v → w.intValuation π = 1 := by
  classical
  haveI := IsPrincipalIdealRing.principal v.asIdeal
  have hspan : Ideal.span {Submodule.IsPrincipal.generator v.asIdeal} = v.asIdeal :=
    Ideal.span_singleton_generator v.asIdeal
  have h0 : Submodule.IsPrincipal.generator v.asIdeal ≠ 0 := fun h ↦
    v.ne_bot (by rw [← hspan, h]; exact Ideal.span_singleton_eq_bot.mpr rfl)
  refine ⟨Submodule.IsPrincipal.generator v.asIdeal, h0,
    intValuation_singleton v h0 hspan.symm, fun w hw ↦ ?_⟩
  rw [intValuation_eq_one_iff]
  intro hmem
  apply hw
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm

theorem finiteIdele_exists_global_profile [IsPrincipalIdealRing R]
    (δ : (FiniteAdeleRing R K)ˣ) :
    ∃ α : Kˣ,
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
          * (δ : FiniteAdeleRing R K)) v ∈ v.adicCompletionIntegers K) ∧
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
          * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v
          ∈ v.adicCompletionIntegers K) := by
  classical
  obtain ⟨hne, hev⟩ := FiniteAdeleRing.isUnit_iff.mp (Units.isUnit δ)
  have hvne : ∀ v : HeightOneSpectrum R, Valued.v ((δ : FiniteAdeleRing R K) v) ≠ 0 :=
    fun v ↦ (Valuation.ne_zero_iff _).mpr (hne v)

  choose π hπ0 hπv hπw using fun v : HeightOneSpectrum R ↦ exists_primeGenerator R v
  obtain ⟨m, hm⟩ : ∃ m : HeightOneSpectrum R → ℤ,
      ∀ v, WithZero.exp (m v) = Valued.v ((δ : FiniteAdeleRing R K) v) :=
    ⟨fun v ↦ WithZero.log (Valued.v ((δ : FiniteAdeleRing R K) v)),
      fun v ↦ WithZero.exp_log (hvne v)⟩

  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum R),
      ∀ w, w ∉ S → Valued.v ((δ : FiniteAdeleRing R K) w) = 1 :=
    ⟨(Filter.eventually_cofinite.mp hev).toFinset,
      fun w hw ↦ by_contra fun h ↦ hw ((Set.Finite.mem_toFinset _).mpr h)⟩
  have hπK : ∀ v, algebraMap R K (π v) ≠ 0 := fun v h ↦
    hπ0 v (IsFractionRing.injective R K (by rw [h, map_zero]))

  set a : K := ∏ v ∈ S, (algebraMap R K (π v)) ^ (-(m v)) with ha
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero _ (hπK v)

  have hval : ∀ w : HeightOneSpectrum R,
      w.valuation K a = Valued.v ((δ : FiniteAdeleRing R K) w) := by
    intro w
    rw [ha, map_prod]
    simp_rw [map_zpow₀]
    rw [Finset.prod_eq_single w]
    · rw [valuation_of_algebraMap, hπv w, ← WithZero.exp_zsmul, ← hm w]
      congr 1
      rw [smul_eq_mul, neg_mul_neg, mul_one]
    · intro v _ hvw
      rw [valuation_of_algebraMap, hπw v w (Ne.symm hvw), _root_.one_zpow]
    · intro hw
      have hm0 : m w = 0 := by
        have h1 := hm w
        rw [hS w hw, WithZero.exp_eq_one] at h1
        exact h1
      rw [hm0, neg_zero, zpow_zero]
  refine ⟨Units.mk0 a ha0, fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [coe_mul_apply, mem_adicCompletionIntegers, Valuation.map_mul,
      valued_algebraMap_finiteAdeleRing_apply, Units.val_inv_eq_inv_val, Units.val_mk0,
      map_inv₀, hval v]
    exact le_of_eq (inv_mul_cancel₀ (hvne v))
  · have hprod : (δ : FiniteAdeleRing R K) v
        * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
      rw [← coe_mul_apply, Units.mul_inv, coe_one_apply]
    rw [coe_mul_apply, mem_adicCompletionIntegers, Valuation.map_mul,
      valued_algebraMap_finiteAdeleRing_apply, Units.val_mk0, hval v]
    exact le_of_eq (by rw [← Valuation.map_mul, hprod, Valuation.map_one])

theorem exists_ratGL_inv_mul_mem_of_finiteIdele
    (hcn : ∀ δ : (FiniteAdeleRing R K)ˣ, ∃ α : Kˣ,
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
          * (δ : FiniteAdeleRing R K)) v ∈ v.adicCompletionIntegers K) ∧
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
          * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v
          ∈ v.adicCompletionIntegers K))
    (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ γ : GL (Fin 2) K, (ratGL R K γ)⁻¹ * g ∈ finiteIntegralGL2 R K := by
  obtain ⟨t, x, z, cu, htint, hg⟩ := exists_gauss_decomposition R K g
  obtain ⟨α, hα₁, hα₂⟩ := hcn (detUnit R K g)

  set w : (FiniteAdeleRing R K)ˣ :=
    (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α)⁻¹
      * detUnit R K g with hw
  have hmapinv :
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α)⁻¹
        = Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α⁻¹ :=
    (map_inv (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)) α).symm
  have hwval : (w : FiniteAdeleRing R K)
      = algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
        * (detUnit R K g : FiniteAdeleRing R K) := by
    rw [hw, hmapinv, Units.val_mul, Units.coe_map]; rfl
  have hwinvval : ((w⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
      = algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
        * (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) := by
    rw [hw, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_comm, Units.coe_map]; rfl
  have hwmem : diagTorusGL2 w ∈ finiteIntegralGL2 R K :=
    diagTorusGL2_mem R K (fun v ↦ by rw [hwval]; exact hα₁ v)
      (fun v ↦ by rw [hwinvval]; exact hα₂ v)

  have hδsplit : diagTorusGL2 (detUnit R K g) = ratGL R K (diagTorusGL2 α) * diagTorusGL2 w := by
    rw [show ratGL R K (diagTorusGL2 α) = diagTorusGL2
        (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α) from
      map_diagTorusGL2 _ _, ← diagTorusGL2_mul, hw]
    congr 1
    group
  have hbase : (ratGL R K (diagTorusGL2 α))⁻¹
      * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t)) ∈ finiteIntegralGL2 R K := by
    have heq : (ratGL R K (diagTorusGL2 α))⁻¹
        * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t))
        = diagTorusGL2 w * lowerUnipGL2 (-t) := by
      rw [hδsplit]; group
    rw [heq]
    refine mul_mem hwmem (lowerUnipGL2_mem R K fun v ↦ ?_)
    rw [coe_neg_apply]
    exact neg_mem (htint v)

  obtain ⟨q₁, hq₁⟩ := absorb_unipotent_left R K hbase z
  obtain ⟨q₂, hq₂⟩ := absorb_lowerUnip_left R K hq₁ (cu : FiniteAdeleRing R K)
  obtain ⟨q₃, hq₃⟩ := absorb_unipotent_left R K hq₂ x
  refine ⟨unipotentGL2 q₃ * (lowerUnipGL2 q₂ * (unipotentGL2 q₁ * diagTorusGL2 α)), ?_⟩
  rw [hg]
  exact hq₃

theorem exists_map_mul_mem_finiteIntegralGL2 [IsPrincipalIdealRing R]
    (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ γ : GL (Fin 2) K,
      GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ * g
        ∈ finiteIntegralGL2 R K := by
  obtain ⟨γ, hγ⟩ := exists_ratGL_inv_mul_mem_of_finiteIdele R K
    (finiteIdele_exists_global_profile R K) g
  refine ⟨γ⁻¹, ?_⟩
  rw [map_inv]
  exact hγ

theorem glFin_globalPoints (γ : GL (Fin 2) K) :
    glFin R K (globalPoints R K γ)
      = GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ := by
  ext i j
  rfl

end NumberField.AdelicLevel.GL2StrongApproxW8M
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField.AdelicLevel P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField.AdelicLevel.GL2StrongApproxW8M"
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField.AdelicLevel"
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField.AdelicLevel P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.NumberField.AdelicLevel.GL2StrongApproxW8M"

theorem solution
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers ℚ) ℚ := by
  haveI : IsPrincipalIdealRing (NumberField.RingOfIntegers ℚ) :=
    NumberField.classNumber_eq_one_iff.mp Rat.classNumber_eq
  obtain ⟨γ, hγ⟩ :=
    NumberField.AdelicLevel.GL2StrongApproxW8M.exists_map_mul_mem_finiteIntegralGL2
      (NumberField.RingOfIntegers ℚ) ℚ g
  refine ⟨γ, ?_⟩
  rw [NumberField.AdelicLevel.GL2StrongApproxW8M.glFin_globalPoints]
  exact hγ

end S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat
end P2MW
export P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat (solution)
