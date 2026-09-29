-- Prove2me | solution 1 for LocalGL2.heckeIndicator_diagPi_mul_localRepInf_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/77ec2dcb-db7b-5df9-8fe1-c6b2b4ac258d

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace HeckePair
p2m_export "HeckePair" "HeckeAlgebra apply_left_mul apply_mul_right ext coe_apply_add coe_apply_smul convTerm_mk support_convTerm_subset mul_apply one_mul mul_one mul_zero smul_mul mul_assoc doubleCoset mem_doubleCoset_iff self_mem_doubleCoset mul_mem_doubleCoset doubleCoset_mul_mem heckeIndicator heckeIndicator_apply_of_mem heckeIndicator_apply_of_notMem"
p2m_open "HeckePair"

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

theorem apply_eq_of_mem_doubleCoset' (f : HeckeAlgebra U R₀) {g x : G}
    (hx : x ∈ doubleCoset U g) : (f : G → R₀) x = (f : G → R₀) g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  rw [apply_mul_right f hv, apply_left_mul f hu]

theorem mem_doubleCoset_comm {g x : G} : x ∈ doubleCoset U g ↔ g ∈ doubleCoset U x := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp h
    exact mem_doubleCoset_iff.mpr ⟨u⁻¹, inv_mem hu, v⁻¹, inv_mem hv, by group⟩
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp h
    exact mem_doubleCoset_iff.mpr ⟨u⁻¹, inv_mem hu, v⁻¹, inv_mem hv, by group⟩

theorem mem_doubleCoset_trans {g x y : G} (hx : x ∈ doubleCoset U g)
    (hy : y ∈ doubleCoset U x) : y ∈ doubleCoset U g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  obtain ⟨u', hu', v', hv', rfl⟩ := mem_doubleCoset_iff.mp hy
  exact mem_doubleCoset_iff.mpr ⟨u' * u, mul_mem hu' hu, v * v', mul_mem hv hv', by group⟩

theorem mem_doubleCoset_iff_of_mem_center' {z x : G} (hz : z ∈ Subgroup.center G) :
    x ∈ doubleCoset U z ↔ z⁻¹ * x ∈ U := by
  rw [mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [(Subgroup.mem_center_iff.mp hz) u, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hu hv
  · intro h
    exact ⟨1, one_mem U, z⁻¹ * x, h, by group⟩

theorem heckeIndicator_mul_apply_eq_sum {ι : Type*} [Fintype ι] {t : G} {reps : ι → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U t reps)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {t}) : Set (G ⧸ U)).Finite)
    (f : HeckeAlgebra U R₀) (x : G) :
    ((heckeIndicator R₀ t hfin * f : HeckeAlgebra U R₀) : G → R₀) x
      = ∑ i, (f : G → R₀) ((reps i)⁻¹ * x) := by
  classical
  rw [mul_apply]
  have hsupp : QuotientGroup.mk '' (Function.support
      ((heckeIndicator R₀ t hfin : HeckeAlgebra U R₀) : G → R₀))
        ⊆ ((Finset.univ.image fun i => (QuotientGroup.mk (reps i) : G ⧸ U)) : Set (G ⧸ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyD : y ∈ doubleCoset U t := by
      by_contra hyD
      exact hy (heckeIndicator_apply_of_notMem hfin hyD)
    obtain ⟨i, hi⟩ := hsys.covers y hyD
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact ⟨i, hi.symm⟩
  rw [finsum_eq_sum_of_support_subset _ ((support_convTerm_subset _ f x).trans hsupp),
    Finset.sum_image (fun i _ j _ h => hsys.mk_injective h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [convTerm_mk, heckeIndicator_apply_of_mem hfin (hsys.mem_doubleCoset i), one_mul]

end

end HeckePair

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup exists_entry_eq_of_mem_integralSubgroup"
p2m_open "LocalGL2"

noncomputable section

section Integral

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem entries_mem_range_mul {x y : GL (Fin 2) K}
    (hx : ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hy : ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) :
    ∀ i j, ((x * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨a, ha⟩ := hx i 0
  obtain ⟨b, hb⟩ := hy 0 j
  obtain ⟨c, hc⟩ := hx i 1
  obtain ⟨d, hd⟩ := hy 1 j
  exact ⟨a * b + c * d, by rw [map_add, map_mul, map_mul, ha, hb, hc, hd]⟩

theorem entries_mem_range_of_mem_integralSubgroup {u : GL (Fin 2) K}
    (hu : u ∈ integralSubgroup R K) :
    ∀ i j, (u : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
  fun i j => exists_entry_eq_of_mem_integralSubgroup hu i j

theorem entries_mem_range_of_mem_doubleCoset {g x : GL (Fin 2) K}
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) g) :
    ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact entries_mem_range_mul (entries_mem_range_mul
    (entries_mem_range_of_mem_integralSubgroup hu) hg) (entries_mem_range_of_mem_integralSubgroup hv)

theorem entries_mem_range_diagPi :
    ∀ i j, ((diagPi ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) := by
  intro i j
  rw [coe_diagPi]
  fin_cases i <;> fin_cases j
  · exact ⟨ϖ, rfl⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

theorem exists_det_eq_of_mem_integralSubgroup {u : GL (Fin 2) K}
    (hu : u ∈ integralSubgroup R K) :
    ∃ η : Rˣ, (u : Matrix (Fin 2) (Fin 2) K).det = algebraMap R K η := by
  obtain ⟨y, rfl⟩ := hu
  refine ⟨Matrix.GeneralLinearGroup.det y, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.GeneralLinearGroup.map_apply, map_sub, map_mul]

theorem exists_det_eq_of_mem_doubleCoset_diagPi {x : GL (Fin 2) K}
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0)) :
    ∃ η : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det = algebraMap R K η * algebraMap R K ϖ := by
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_integralSubgroup hu
  obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_integralSubgroup hv
  refine ⟨η₁ * η₂, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h₁, h₂, coe_diagPi,
    Matrix.det_fin_two_of, Units.val_mul, map_mul]
  ring

theorem coe_diagPi_mul_coe_localRepInf' :
    (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagPi_mul_localRepInf_mem_center' :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  simp only [Units.val_mul]
  rw [coe_diagPi_mul_coe_localRepInf', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem diagPi_mul_localRepInf_mul_apply (m : GL (Fin 2) K) (i j : Fin 2) :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      = algebraMap R K ϖ * (m : Matrix (Fin 2) (Fin 2) K) i j := by
  rw [Units.val_mul, Units.val_mul, coe_diagPi_mul_coe_localRepInf', Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]

theorem coe_localRepInf_sq :
    ((localRepInf ϖ hϖ0 ^ 2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![1, 0; 0, algebraMap R K ϖ ^ 2] := by
  rw [pow_two, Units.val_mul, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two]

theorem localRepInf_mem_doubleCoset_diagPi :
    localRepInf ϖ hϖ0 ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) :=
  HeckePair.mem_doubleCoset_iff.mpr ⟨weylInt R K, weylInt_mem, weylInt R K, weylInt_mem, rfl⟩

def localReps : Option (R ⧸ Ideal.span {ϖ}) → GL (Fin 2) K
  | some c => localRepSome ϖ hϖ0 (Quotient.out c)
  | none => localRepInf ϖ hϖ0

@[scoped simp] theorem localReps_some (c : R ⧸ Ideal.span {ϖ}) :
    localReps ϖ hϖ0 (some c) = localRepSome ϖ hϖ0 (Quotient.out c) := rfl

@[scoped simp] theorem localReps_none : localReps ϖ hϖ0 none = localRepInf ϖ hϖ0 := rfl

end Integral

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem algebraMap_mul_ne_one (hϖ : ¬ IsUnit ϖ) (r : R) :
    algebraMap R K ϖ * algebraMap R K r ≠ 1 := by
  intro h
  apply hϖ
  rw [← map_mul, ← map_one (algebraMap R K)] at h
  exact IsUnit.of_mul_eq_one r (IsFractionRing.injective R K h)

theorem dvd_of_not_isUnit (hϖ : Irreducible ϖ) {r : R} (hr : ¬ IsUnit r) : ϖ ∣ r := by
  rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal]
  exact hr

theorem isHeckeCosetSystem_localReps (hϖ : Irreducible ϖ) :
    HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup R K) (diagPi ϖ hϖ0)
      (localReps ϖ hϖ0) := by
  constructor
  · rintro (_ | c)
    · exact localRepInf_mem_doubleCoset_diagPi ϖ hϖ0
    · exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨unipotentInt K (Quotient.out c), unipotentInt_mem _, 1, one_mem _,
          by rw [mul_one]; rfl⟩
  · intro x hx
    obtain ⟨y, hy, u, hu, rfl⟩ := Set.mem_mul.mp hx
    have hu' : u ∈ integralSubgroup R K := hu
    have hy' : y ∈ heckeMulSet ϖ hϖ0 := hy
    have hmkx : (QuotientGroup.mk (y * u) : GL (Fin 2) K ⧸ integralSubgroup R K)
        = QuotientGroup.mk y := QuotientGroup.mk_mul_of_mem y hu'
    rcases exists_rep_of_mem_heckeMulSet ϖ hϖ0 hϖ hy' with ⟨b, hb⟩ | hbinf
    · refine ⟨some (Ideal.Quotient.mk _ b), ?_⟩
      rw [hmkx, ← hb, localReps_some]
      refine mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 ?_
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    · exact ⟨none, by rw [hmkx, ← hbinf, localReps_none]⟩
  · rintro (_ | c) (_ | c') h
    · rfl
    · simp only [localReps_some, localReps_none] at h
      exact absurd h.symm (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖ.not_isUnit _)
    · simp only [localReps_some, localReps_none] at h
      exact absurd h (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖ.not_isUnit _)
    · simp only [localReps_some] at h
      have hd := dvd_sub_of_mk_localRepSome_eq ϖ hϖ0 h
      rw [← Ideal.Quotient.mk_out c, ← Ideal.Quotient.mk_out c']
      exact congrArg some (Ideal.Quotient.eq.mpr (by rwa [Ideal.mem_span_singleton, dvd_sub_comm]))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem mem_doubleCoset_localRepInf_sq_of_isUnit {x : GL (Fin 2) K}
    (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdet : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ 2) (ha : IsUnit (e 0 0)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
  obtain ⟨au, hau⟩ := ha
  set a' : R := ↑au⁻¹ with ha'
  have h1 : e 0 0 * a' = 1 := by rw [← hau, ha', Units.mul_inv]
  have hdet1 : IsUnit (Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a']) := by
    have : Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a'] = ε := by
      rw [Matrix.det_fin_two_of]; linear_combination (ε : R) * h1
    rw [this]; exact ε.isUnit
  have hdet2 : IsUnit (Matrix.det !![(1 : R), e 0 1 * a'; 0, 1]) := by
    rw [Matrix.det_fin_two_of]; simp
  set y₁ := Matrix.GeneralLinearGroup.mk'' _ hdet1 with hy₁
  set y₂ := Matrix.GeneralLinearGroup.mk'' _ hdet2 with hy₂
  have hA : algebraMap R K (e 0 0) * algebraMap R K a' = 1 := by
    rw [← map_mul, h1, map_one]
  have hD : algebraMap R K (e 0 0) * algebraMap R K (e 1 1)
      - algebraMap R K (e 0 1) * algebraMap R K (e 1 0)
        = algebraMap R K ε * algebraMap R K ϖ ^ 2 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul, map_pow]
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨Matrix.GeneralLinearGroup.map (algebraMap R K) y₁, ⟨y₁, rfl⟩,
      Matrix.GeneralLinearGroup.map (algebraMap R K) y₂, ⟨y₂, rfl⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hy₁v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₁ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![e 0 0, 0; e 1 0, (ε : R) * a'] i j) :=
    fun i j => rfl
  have hy₂v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₂ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![(1 : R), e 0 1 * a'; 0, 1] i j) :=
    fun i j => rfl
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, coe_localRepInf_sq, ← he i j]
  simp only [hy₁v, hy₂v]
  fin_cases i <;> fin_cases j <;> simp [map_mul]
  · linear_combination (algebraMap R K (e 0 1)) * hA
  · linear_combination (algebraMap R K (e 1 1)) * hA - (algebraMap R K a') * hD

theorem mem_doubleCoset_sq_or_center (hϖ : Irreducible ϖ) {x : GL (Fin 2) K}
    (hint : ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
      = algebraMap R K ε * algebraMap R K ϖ ^ 2) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) ∨
      x ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) := by
  have hint' : ∀ i j, ∃ r, algebraMap R K r = (x : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => hint i j
  choose e he using hint'
  obtain ⟨ε, hε⟩ := hdet
  have hinj := IsFractionRing.injective R K
  have hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ 2 := by
    apply hinj
    rw [map_sub, map_mul, map_mul, he, he, he, he, map_mul, map_pow, ← hε, Matrix.det_fin_two]
  have hwU : weylInt R K ∈ integralSubgroup R K := weylInt_mem

  by_cases ha : IsUnit (e 0 0)
  · exact Or.inl (mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0 e he ε hdetR ha)

  by_cases hb : IsUnit (e 0 1)
  · left
    have hmem : x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
      refine mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0
        (Matrix.of fun i j => e i (Equiv.swap 0 1 j)) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hb
    have := HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)
    rwa [mul_inv_cancel_right] at this

  by_cases hc : IsUnit (e 1 0)
  · left
    have hmem : weylInt R K * x
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
      refine mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) j) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hc
    have := HeckePair.mul_mem_doubleCoset hmem (inv_mem hwU)
    rwa [inv_mul_cancel_left] at this

  by_cases hd : IsUnit (e 1 1)
  · left
    have hmem : weylInt R K * x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) := by
      refine mem_doubleCoset_localRepInf_sq_of_isUnit ϖ hϖ0
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) (Equiv.swap 0 1 j)) (fun i j => ?_) ε ?_ ?_
      · rw [Units.val_mul, Units.val_mul, coe_weylInt]
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i <;> fin_cases j <;> simp [he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
        linear_combination hdetR
      · simpa using hd
    have h' := HeckePair.mul_mem_doubleCoset
      (HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)) (inv_mem hwU)
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at h'

  right
  have hdvd : ∀ i j, ϖ ∣ e i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact dvd_of_not_isUnit ϖ hϖ ha
    · exact dvd_of_not_isUnit ϖ hϖ hb
    · exact dvd_of_not_isUnit ϖ hϖ hc
    · exact dvd_of_not_isUnit ϖ hϖ hd
  choose e₁ he₁ using hdvd
  have hdet₁ : e₁ 0 0 * e₁ 1 1 - e₁ 0 1 * e₁ 1 0 = ε := by
    have hϖ2 : ϖ ^ 2 ≠ 0 := pow_ne_zero 2 hϖ.ne_zero
    apply mul_left_cancel₀ hϖ2
    rw [← hdetR.trans (mul_comm _ _), he₁ 0 0, he₁ 1 1, he₁ 0 1, he₁ 1 0]
    ring
  have hdetu : IsUnit (Matrix.det (Matrix.of e₁)) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    rw [hdet₁]
    exact ε.isUnit
  set y := Matrix.GeneralLinearGroup.mk'' _ hdetu with hy
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨1, one_mem _, Matrix.GeneralLinearGroup.map (algebraMap R K) y, ⟨y, rfl⟩, ?_⟩
  rw [one_mul]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [diagPi_mul_localRepInf_mul_apply, ← he i j, he₁ i j, map_mul]
  rfl

theorem heckeIndicator_diagPi_mul_self_impl
    (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (h2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ 2}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
      = (HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ 2) h2 :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀)
        + ((Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) + 1)
          • HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hsys := isHeckeCosetSystem_localReps ϖ hϖ0 hϖ
  have hz := diagPi_mul_localRepInf_mem_center' ϖ hϖ0
  have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g := Subgroup.mem_center_iff.mp hz

  have hTint : ∀ {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) →
        ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
    fun hy => entries_mem_range_of_mem_doubleCoset (entries_mem_range_diagPi ϖ hϖ0) hy

  have hl2z : localRepInf ϖ hϖ0 ^ 2
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) := by
    intro h
    have hm := (HeckePair.mem_doubleCoset_iff_of_mem_center' hz).mp h
    obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup hm 0 0
    have key : ((localRepInf ϖ hϖ0 ^ 2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
        = algebraMap R K ϖ * algebraMap R K r := by
      rw [hr, ← diagPi_mul_localRepInf_mul_apply ϖ hϖ0, mul_inv_cancel_left]
    rw [coe_localRepInf_sq] at key
    exact algebraMap_mul_ne_one ϖ hϖ.not_isUnit r (by simpa using key.symm)
  have hzl2 : diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2) :=
    fun h => hl2z (HeckePair.mem_doubleCoset_comm.mp h)
  ext x
  simp only [HeckePair.coe_apply_add, HeckePair.coe_apply_smul]
  by_cases hx2 : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ 2)
  ·
    have hxz : x ∉ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) :=
      fun h => hl2z (HeckePair.mem_doubleCoset_trans h (HeckePair.mem_doubleCoset_comm.mp hx2))
    rw [HeckePair.heckeIndicator_apply_of_mem h2 hx2,
      HeckePair.heckeIndicator_apply_of_notMem hS hxz, mul_zero, add_zero]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hx2]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys, Fintype.sum_option, localReps_none,
      pow_two, inv_mul_cancel_left,
      HeckePair.heckeIndicator_apply_of_mem _ (localRepInf_mem_doubleCoset_diagPi ϖ hϖ0)]
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [localReps_some]
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_

    obtain ⟨r, hr⟩ := hTint hmem 0 0
    rw [Units.val_mul, ← pow_two, coe_localRepSome_inv, coe_localRepInf_sq] at hr
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hr
    exact algebraMap_mul_ne_one ϖ hϖ.not_isUnit r (by rw [hr, mul_inv_cancel₀ hϖ0])
  by_cases hxz : x ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem h2 hx2,
      HeckePair.heckeIndicator_apply_of_mem hS hxz, zero_add, mul_one]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hxz]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys]
    have hterm : ∀ i, ((HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0)
        (finite_image_mul_diagPi ϖ hϖ0 hϖ) :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀)
            ((localReps ϖ hϖ0 i)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)) = 1 := by
      intro i
      refine HeckePair.heckeIndicator_apply_of_mem _ ?_
      obtain ⟨u, hu, v, hv, huv⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
      rw [← huv, _root_.mul_inv_rev, _root_.mul_inv_rev]
      simp only [mul_assoc]
      rw [hzc u⁻¹]
      simp only [mul_assoc]
      rw [inv_mul_cancel_left]

      exact HeckePair.mul_mem_doubleCoset
        (HeckePair.doubleCoset_mul_mem (localRepInf_mem_doubleCoset_diagPi ϖ hϖ0) (inv_mem hu))
        (inv_mem hv)
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul,
      mul_one, Nat.cast_add, Nat.cast_one, Nat.card_eq_fintype_card]
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem h2 hx2,
      HeckePair.heckeIndicator_apply_of_notMem hS hxz, mul_zero, add_zero,
      HeckePair.heckeIndicator_mul_apply_eq_sum hsys]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_
    have hri := hsys.mem_doubleCoset i

    have hx_eq : x = localReps ϖ hϖ0 i * ((localReps ϖ hϖ0 i)⁻¹ * x) := by
      rw [mul_inv_cancel_left]
    have hint : ∀ i' j', (x : Matrix (Fin 2) (Fin 2) K) i' j' ∈ Set.range (algebraMap R K) := by
      rw [hx_eq]
      exact entries_mem_range_mul (hTint hri) (hTint hmem)
    have hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
        = algebraMap R K ε * algebraMap R K ϖ ^ 2 := by
      obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_doubleCoset_diagPi ϖ hϖ0 hri
      obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_doubleCoset_diagPi ϖ hϖ0 hmem
      refine ⟨η₁ * η₂, ?_⟩
      rw [hx_eq, Units.val_mul, Matrix.det_mul, h₁, h₂, Units.val_mul, map_mul]
      ring
    rcases mem_doubleCoset_sq_or_center ϖ hϖ0 hϖ hint hdet with h | h
    · exact hx2 h
    · exact hxz h

end DVR

end

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.LocalGL2"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem coe_unipotentInt weylInt weylInt_mem coe_weylInt diagPi coe_diagPi localRepSome localRepInf coe_localRepInf coe_localRepSome_inv heckeMulSet dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup exists_entry_eq_of_mem_integralSubgroup"
p2m_open "LocalGL2"

noncomputable section

section RecursionBasic

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem diag_two_pow' (x y : K) (n : ℕ) :
    (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) K) ^ n = !![x ^ n, 0; 0, y ^ n] := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem coe_localRepInf_pow (m : ℕ) :
    ((localRepInf ϖ hϖ0 ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![1, 0; 0, algebraMap R K ϖ ^ m] := by
  rw [Units.val_pow_eq_pow_val, coe_localRepInf, diag_two_pow', one_pow]

theorem entries_mem_range_localRepInf_pow (m : ℕ) :
    ∀ i j, ((localRepInf ϖ hϖ0 ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) := by
  intro i j
  rw [coe_localRepInf_pow]
  fin_cases i <;> fin_cases j
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨ϖ ^ m, by simp⟩

theorem exists_det_eq_of_mem_doubleCoset_localRepInf_pow (m : ℕ) {x : GL (Fin 2) K}
    (hx : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m)) :
    ∃ η : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
      = algebraMap R K η * algebraMap R K ϖ ^ m := by
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_integralSubgroup hu
  obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_integralSubgroup hv
  refine ⟨η₁ * η₂, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h₁, h₂,
    coe_localRepInf_pow, Matrix.det_fin_two_of, Units.val_mul, map_mul]
  ring

theorem diagPi_mul_localRepInf_comm :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = localRepInf ϖ hϖ0 * diagPi ϖ hϖ0 := by
  apply Units.ext
  change (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
    = (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
  rw [coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end RecursionBasic
p2m_reactivate "P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.LocalGL2"

section RecursionDVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem center_mul_not_mem_doubleCoset_localRepInf_pow (hϖu : ¬ IsUnit ϖ) (m : ℕ)
    {y : GL (Fin 2) K}
    (hy : ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * y
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
  intro h
  have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g :=
    Subgroup.mem_center_iff.mp (diagPi_mul_localRepInf_mem_center' ϖ hϖ0)
  obtain ⟨u, hu, v, hv, huv⟩ :=
    HeckePair.mem_doubleCoset_iff.mp (HeckePair.mem_doubleCoset_comm.mp h)

  have hint : ∀ i j, ((u * (y * v) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      ∈ Set.range (algebraMap R K) :=
    entries_mem_range_mul (entries_mem_range_of_mem_integralSubgroup hu)
      (entries_mem_range_mul hy (entries_mem_range_of_mem_integralSubgroup hv))
  obtain ⟨r, hr⟩ := hint 0 0
  have key := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) huv
  rw [← mul_assoc, hzc u, mul_assoc, mul_assoc, diagPi_mul_localRepInf_mul_apply, ← hr,
    coe_localRepInf_pow] at key
  exact algebraMap_mul_ne_one ϖ hϖu r (by simpa using key)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem mem_doubleCoset_localRepInf_pow_of_isUnit (m : ℕ) {x : GL (Fin 2) K}
    (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdet : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ m) (ha : IsUnit (e 0 0)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
  obtain ⟨au, hau⟩ := ha
  set a' : R := ↑au⁻¹ with ha'
  have h1 : e 0 0 * a' = 1 := by rw [← hau, ha', Units.mul_inv]
  have hdet1 : IsUnit (Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a']) := by
    have : Matrix.det !![e 0 0, 0; e 1 0, (ε : R) * a'] = ε := by
      rw [Matrix.det_fin_two_of]; linear_combination (ε : R) * h1
    rw [this]; exact ε.isUnit
  have hdet2 : IsUnit (Matrix.det !![(1 : R), e 0 1 * a'; 0, 1]) := by
    rw [Matrix.det_fin_two_of]; simp
  set y₁ := Matrix.GeneralLinearGroup.mk'' _ hdet1 with hy₁
  set y₂ := Matrix.GeneralLinearGroup.mk'' _ hdet2 with hy₂
  have hA : algebraMap R K (e 0 0) * algebraMap R K a' = 1 := by
    rw [← map_mul, h1, map_one]
  have hD : algebraMap R K (e 0 0) * algebraMap R K (e 1 1)
      - algebraMap R K (e 0 1) * algebraMap R K (e 1 0)
        = algebraMap R K ε * algebraMap R K ϖ ^ m := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul, map_pow]
  refine HeckePair.mem_doubleCoset_iff.mpr
    ⟨Matrix.GeneralLinearGroup.map (algebraMap R K) y₁, ⟨y₁, rfl⟩,
      Matrix.GeneralLinearGroup.map (algebraMap R K) y₂, ⟨y₂, rfl⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hy₁v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₁ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![e 0 0, 0; e 1 0, (ε : R) * a'] i j) :=
    fun i j => rfl
  have hy₂v : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap R K) y₂ :
      Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K (!![(1 : R), e 0 1 * a'; 0, 1] i j) :=
    fun i j => rfl
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, coe_localRepInf_pow, ← he i j]
  simp only [hy₁v, hy₂v]
  fin_cases i <;> fin_cases j <;> simp [map_mul]
  · linear_combination (algebraMap R K (e 0 1)) * hA
  · linear_combination (algebraMap R K (e 1 1)) * hA - (algebraMap R K a') * hD

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem mem_doubleCoset_localRepInf_pow_of_exists_isUnit (m : ℕ) {x : GL (Fin 2) K}
    (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ m)
    (hunit : IsUnit (e 0 0) ∨ IsUnit (e 0 1) ∨ IsUnit (e 1 0) ∨ IsUnit (e 1 1)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
  have hwU : weylInt R K ∈ integralSubgroup R K := weylInt_mem
  rcases hunit with ha | hb | hc | hd
  · exact mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m e he ε hdetR ha
  · have hmem : x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
      refine mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m
        (Matrix.of fun i j => e i (Equiv.swap 0 1 j)) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hb
    have := HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)
    rwa [mul_inv_cancel_right] at this
  · have hmem : weylInt R K * x
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
      refine mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) j) (fun i j => ?_) (-ε) ?_ ?_
      · rw [Units.val_mul, coe_weylInt]
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Units.val_neg]
        linear_combination (-1 : R) * hdetR
      · simpa using hc
    have := HeckePair.mul_mem_doubleCoset hmem (inv_mem hwU)
    rwa [inv_mul_cancel_left] at this
  · have hmem : weylInt R K * x * weylInt R K
        ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) := by
      refine mem_doubleCoset_localRepInf_pow_of_isUnit ϖ hϖ0 m
        (Matrix.of fun i j => e (Equiv.swap 0 1 i) (Equiv.swap 0 1 j)) (fun i j => ?_) ε ?_ ?_
      · rw [Units.val_mul, Units.val_mul, coe_weylInt]
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i <;> fin_cases j <;> simp [he]
      · simp only [Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
        linear_combination hdetR
      · simpa using hd
    have h' := HeckePair.mul_mem_doubleCoset
      (HeckePair.doubleCoset_mul_mem hmem (inv_mem hwU)) (inv_mem hwU)
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at h'

omit [IsFractionRing R K] in

theorem exists_eq_center_mul_of_forall_not_isUnit (hϖ : Irreducible ϖ) (m : ℕ)
    {x : GL (Fin 2) K} (e : Matrix (Fin 2) (Fin 2) R)
    (he : ∀ i j, algebraMap R K (e i j) = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (ε : Rˣ) (hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ (m + 2))
    (hnot : ¬ (IsUnit (e 0 0) ∨ IsUnit (e 0 1) ∨ IsUnit (e 1 0) ∨ IsUnit (e 1 1))) :
    ∃ (x' : GL (Fin 2) K) (e' : Matrix (Fin 2) (Fin 2) R),
      x = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x' ∧
      (∀ i j, algebraMap R K (e' i j) = (x' : Matrix (Fin 2) (Fin 2) K) i j) ∧
      e' 0 0 * e' 1 1 - e' 0 1 * e' 1 0 = ε * ϖ ^ m := by
  simp only [not_or] at hnot
  obtain ⟨ha, hb, hc, hd⟩ := hnot
  have hdvd : ∀ i j, ϖ ∣ e i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact dvd_of_not_isUnit ϖ hϖ ha
    · exact dvd_of_not_isUnit ϖ hϖ hb
    · exact dvd_of_not_isUnit ϖ hϖ hc
    · exact dvd_of_not_isUnit ϖ hϖ hd
  choose e₁ he₁ using hdvd
  refine ⟨(diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x, Matrix.of e₁, by rw [mul_inv_cancel_left],
    fun i j => ?_, ?_⟩
  ·
    have h := diagPi_mul_localRepInf_mul_apply ϖ hϖ0
      ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x) i j
    rw [mul_inv_cancel_left, ← he i j, he₁ i j, map_mul] at h
    exact mul_left_cancel₀ hϖ0 h
  · have hϖ2 : ϖ ^ 2 ≠ 0 := pow_ne_zero 2 hϖ.ne_zero
    apply mul_left_cancel₀ hϖ2
    simp only [Matrix.of_apply]
    rw [show ϖ ^ 2 * (↑ε * ϖ ^ m) = ↑ε * ϖ ^ (m + 2) by ring, ← hdetR, he₁ 0 0, he₁ 1 1,
      he₁ 0 1, he₁ 1 0]
    ring

theorem mem_doubleCoset_or_of_det (hϖ : Irreducible ϖ) (k : ℕ) {x : GL (Fin 2) K}
    (hint : ∀ i j, (x : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
    (hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
      = algebraMap R K ε * algebraMap R K ϖ ^ (k + 3)) :
    x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ (k + 3)) ∨
      x ∈ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) ∨
      ∃ x'' : GL (Fin 2) K,
        (∀ i j, (x'' : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) ∧
        x = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x'') := by
  have hint' : ∀ i j, ∃ r, algebraMap R K r = (x : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => hint i j
  choose e he using hint'
  obtain ⟨ε, hε⟩ := hdet
  have hinj := IsFractionRing.injective R K
  have hdetR : e 0 0 * e 1 1 - e 0 1 * e 1 0 = ε * ϖ ^ (k + 3) := by
    apply hinj
    rw [map_sub, map_mul, map_mul, he, he, he, he, map_mul, map_pow, ← hε, Matrix.det_fin_two]
  by_cases hunit : IsUnit (e 0 0) ∨ IsUnit (e 0 1) ∨ IsUnit (e 1 0) ∨ IsUnit (e 1 1)
  · exact Or.inl (mem_doubleCoset_localRepInf_pow_of_exists_isUnit ϖ hϖ0 (k + 3) e he ε hdetR hunit)
  obtain ⟨x', e', hx', he', hdet'⟩ :=
    exists_eq_center_mul_of_forall_not_isUnit ϖ hϖ0 hϖ (k + 1) e he ε hdetR hunit
  by_cases hunit' : IsUnit (e' 0 0) ∨ IsUnit (e' 0 1) ∨ IsUnit (e' 1 0) ∨ IsUnit (e' 1 1)
  · right; left
    have hm := mem_doubleCoset_localRepInf_pow_of_exists_isUnit ϖ hϖ0 (k + 1) e' he' ε hdet' hunit'
    obtain ⟨u, hu, v, hv, huv⟩ := HeckePair.mem_doubleCoset_iff.mp hm
    have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
        = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g :=
      Subgroup.mem_center_iff.mp (diagPi_mul_localRepInf_mem_center' ϖ hϖ0)
    refine HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, v, hv, ?_⟩
    have hl2 : localRepInf ϖ hϖ0 ^ (k + 2) = localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1) :=
      pow_succ' _ _
    rw [hx', ← huv, hl2, ← mul_assoc (diagPi ϖ hϖ0), ← mul_assoc u, hzc u]
    simp only [mul_assoc]
  · right; right

    simp only [not_or] at hunit'
    obtain ⟨ha, hb, hc, hd⟩ := hunit'
    have hdvd : ∀ i j, ϖ ∣ e' i j := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact dvd_of_not_isUnit ϖ hϖ ha
      · exact dvd_of_not_isUnit ϖ hϖ hb
      · exact dvd_of_not_isUnit ϖ hϖ hc
      · exact dvd_of_not_isUnit ϖ hϖ hd
    choose e₁ he₁ using hdvd
    refine ⟨(diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x', fun i j => ?_, ?_⟩
    · have h := diagPi_mul_localRepInf_mul_apply ϖ hϖ0
        ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * x') i j
      rw [mul_inv_cancel_left, ← he' i j, he₁ i j, map_mul] at h
      exact ⟨e₁ i j, mul_left_cancel₀ hϖ0 h⟩
    · rw [mul_inv_cancel_left, hx']

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem localRepSome_inv_mul_diagPi_mul_localRepInf_pow (c : R) (k : ℕ) :
    (localRepSome ϖ hϖ0 c)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
      = localRepInf ϖ hϖ0 ^ (k + 2) * unipotentInt K (-(c * ϖ ^ (k + 1))) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_localRepSome_inv, coe_diagPi,
    coe_localRepInf_pow, coe_unipotentInt, map_neg, map_mul, map_pow]
  set π : K := algebraMap R K ϖ with hπdef
  set c' : K := algebraMap R K c with hc'def
  have hπ : π⁻¹ * π ^ (k + 2) = π ^ (k + 1) := by
    rw [pow_succ' _ (k + 1), inv_mul_cancel_left₀ hϖ0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hϖ0]
  rw [mul_assoc, hπ]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem diagPi_mul_localRepInf_pow_succ (k : ℕ) :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1) := by
  rw [mul_assoc]
  congr 1
  exact pow_succ' _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem localRepInf_inv_mul_diagPi_mul_localRepInf_pow (k : ℕ) :
    (localRepInf ϖ hϖ0)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ k := by
  have hl1 : localRepInf ϖ hϖ0 ^ (k + 1) = localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ k :=
    pow_succ' _ _
  calc (localRepInf ϖ hϖ0)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
      = (localRepInf ϖ hϖ0)⁻¹ * (localRepInf ϖ hϖ0 * diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1)) := by
        rw [diagPi_mul_localRepInf_pow_succ, diagPi_mul_localRepInf_comm]
    _ = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 1) := by rw [mul_assoc, inv_mul_cancel_left]
    _ = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ k := by rw [hl1, ← mul_assoc]

theorem heckeIndicator_diagPi_mul_localRepInf_pow_impl
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀] (k : ℕ)
    (hk2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 2)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hk3 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 3)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hSk : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)}) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) hk2
      = (HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 3)) hk3 :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀)
        + (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀)
          • HeckePair.heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) hSk := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hsys := isHeckeCosetSystem_localReps ϖ hϖ0 hϖ
  have hz := diagPi_mul_localRepInf_mem_center' ϖ hϖ0
  have hzc : ∀ g : GL (Fin 2) K, g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)
      = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g := Subgroup.mem_center_iff.mp hz

  have hTint : ∀ {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) →
        ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
    fun hy => entries_mem_range_of_mem_doubleCoset (entries_mem_range_diagPi ϖ hϖ0) hy
  have hLint : ∀ (m : ℕ) {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ m) →
        ∀ i j, (y : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) :=
    fun m {_} hy => entries_mem_range_of_mem_doubleCoset (entries_mem_range_localRepInf_pow ϖ hϖ0 m) hy

  have hBz : ∀ {y : GL (Fin 2) K},
      y ∈ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) →
        ∃ y' : GL (Fin 2) K,
          (∀ i j, (y' : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K)) ∧
          y = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * y' := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
    refine ⟨u * (localRepInf ϖ hϖ0 ^ (k + 1) * v),
      entries_mem_range_mul (entries_mem_range_of_mem_integralSubgroup hu)
        (entries_mem_range_mul (entries_mem_range_localRepInf_pow ϖ hϖ0 (k + 1))
          (entries_mem_range_of_mem_integralSubgroup hv)), ?_⟩
    rw [diagPi_mul_localRepInf_pow_succ, ← mul_assoc (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0),
      ← hzc u]
    simp only [mul_assoc]

  have hAB : localRepInf ϖ hϖ0 ^ (k + 3)
      ∉ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) := by
    intro h
    obtain ⟨y', hy', hyy⟩ := hBz h
    exact center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 3) hy'
      (by rw [← hyy]; exact HeckePair.self_mem_doubleCoset _)
  have hBA : diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)
      ∉ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ (k + 3)) := by
    rw [diagPi_mul_localRepInf_pow_succ]
    exact center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 3)
      (entries_mem_range_localRepInf_pow ϖ hϖ0 (k + 1))
  ext x
  simp only [HeckePair.coe_apply_add, HeckePair.coe_apply_smul]
  by_cases hxA : x ∈ HeckePair.doubleCoset (integralSubgroup R K) (localRepInf ϖ hϖ0 ^ (k + 3))
  ·
    have hxB : x ∉ HeckePair.doubleCoset (integralSubgroup R K)
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) :=
      fun h => hAB (HeckePair.mem_doubleCoset_trans h (HeckePair.mem_doubleCoset_comm.mp hxA))
    rw [HeckePair.heckeIndicator_apply_of_mem hk3 hxA,
      HeckePair.heckeIndicator_apply_of_notMem hSk hxB, mul_zero, add_zero]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hxA]
    have hnone : (localRepInf ϖ hϖ0)⁻¹ * localRepInf ϖ hϖ0 ^ (k + 3) = localRepInf ϖ hϖ0 ^ (k + 2) := by
      have hl3 : localRepInf ϖ hϖ0 ^ (k + 3) = localRepInf ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2) :=
        pow_succ' _ _
      rw [hl3, inv_mul_cancel_left]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys, Fintype.sum_option, localReps_none, hnone,
      HeckePair.heckeIndicator_apply_of_mem _ (HeckePair.self_mem_doubleCoset _)]
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [localReps_some]
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_

    obtain ⟨r, hr⟩ := hLint (k + 2) hmem 0 0
    rw [Units.val_mul, coe_localRepSome_inv, coe_localRepInf_pow] at hr
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hr
    exact algebraMap_mul_ne_one ϖ hϖ.not_isUnit r (by rw [hr, mul_inv_cancel₀ hϖ0])
  by_cases hxB : x ∈ HeckePair.doubleCoset (integralSubgroup R K)
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem hk3 hxA,
      HeckePair.heckeIndicator_apply_of_mem hSk hxB, zero_add, mul_one]
    conv_lhs => rw [HeckePair.apply_eq_of_mem_doubleCoset' _ hxB]
    rw [HeckePair.heckeIndicator_mul_apply_eq_sum hsys, Fintype.sum_option, localReps_none,
      localRepInf_inv_mul_diagPi_mul_localRepInf_pow,
      HeckePair.heckeIndicator_apply_of_notMem _
        (center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 2)
          (entries_mem_range_localRepInf_pow ϖ hϖ0 k)), zero_add]
    have hterm : ∀ c : R ⧸ Ideal.span {ϖ},
        ((HeckePair.heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) hk2 :
          HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀)
            ((localReps ϖ hϖ0 (some c))⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2))) = 1 := by
      intro c
      rw [localReps_some, localRepSome_inv_mul_diagPi_mul_localRepInf_pow]
      exact HeckePair.heckeIndicator_apply_of_mem _
        (HeckePair.doubleCoset_mul_mem (HeckePair.self_mem_doubleCoset _) (unipotentInt_mem _))
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  ·
    rw [HeckePair.heckeIndicator_apply_of_notMem hk3 hxA,
      HeckePair.heckeIndicator_apply_of_notMem hSk hxB, mul_zero, add_zero,
      HeckePair.heckeIndicator_mul_apply_eq_sum hsys]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine HeckePair.heckeIndicator_apply_of_notMem _ fun hmem => ?_
    have hri := hsys.mem_doubleCoset i

    have hx_eq : x = localReps ϖ hϖ0 i * ((localReps ϖ hϖ0 i)⁻¹ * x) := by
      rw [mul_inv_cancel_left]
    have hint : ∀ i' j', (x : Matrix (Fin 2) (Fin 2) K) i' j' ∈ Set.range (algebraMap R K) := by
      rw [hx_eq]
      exact entries_mem_range_mul (hTint hri) (hLint (k + 2) hmem)
    have hdet : ∃ ε : Rˣ, (x : Matrix (Fin 2) (Fin 2) K).det
        = algebraMap R K ε * algebraMap R K ϖ ^ (k + 3) := by
      obtain ⟨η₁, h₁⟩ := exists_det_eq_of_mem_doubleCoset_diagPi ϖ hϖ0 hri
      obtain ⟨η₂, h₂⟩ := exists_det_eq_of_mem_doubleCoset_localRepInf_pow ϖ hϖ0 (k + 2) hmem
      refine ⟨η₁ * η₂, ?_⟩
      rw [hx_eq, Units.val_mul, Matrix.det_mul, h₁, h₂, Units.val_mul, map_mul]
      ring
    rcases mem_doubleCoset_or_of_det ϖ hϖ0 hϖ k hint hdet with h | h | ⟨x'', hx'', hxx⟩
    · exact hxA h
    · exact hxB h
    ·
      have hzr : ∀ i' j', ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (localReps ϖ hϖ0 i)⁻¹ * x'' :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i' j' ∈ Set.range (algebraMap R K) := by
        refine entries_mem_range_mul (fun i' j' => ?_) hx''
        cases i with
        | none =>
          rw [localReps_none, mul_inv_cancel_right]
          exact entries_mem_range_diagPi ϖ hϖ0 i' j'
        | some c =>
          rw [localReps_some, Units.val_mul, coe_localRepSome_inv, Units.val_mul, coe_diagPi,
            coe_localRepInf]
          set π : K := algebraMap R K ϖ with hπdef
          have h00 : π * π⁻¹ = 1 := mul_inv_cancel₀ hϖ0
          fin_cases i' <;> fin_cases j'
          · exact ⟨1, by simp [Matrix.mul_apply, Fin.sum_univ_two, h00]⟩
          · refine ⟨-Quotient.out c, ?_⟩
            simp [Matrix.mul_apply, Fin.sum_univ_two]
            rw [hπdef, mul_comm, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one]
          · exact ⟨0, by simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
          · exact ⟨ϖ, by simp [Matrix.mul_apply, Fin.sum_univ_two, hπdef]⟩
      refine center_mul_not_mem_doubleCoset_localRepInf_pow ϖ hϖ0 hϖ.not_isUnit (k + 2) hzr ?_
      have : (localReps ϖ hϖ0 i)⁻¹ * x
          = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
            * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (localReps ϖ hϖ0 i)⁻¹ * x'') := by
        rw [hxx]
        calc (localReps ϖ hϖ0 i)⁻¹
              * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x''))
            = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
                * ((localReps ϖ hϖ0 i)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * x'')) := by
              rw [← mul_assoc, hzc, mul_assoc]
          _ = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0
                * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (localReps ϖ hϖ0 i)⁻¹ * x'') := by
              rw [← mul_assoc ((localReps ϖ hϖ0 i)⁻¹), hzc]
      rw [← this]
      exact hmem

end RecursionDVR
p2m_reactivate "P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.LocalGL2"

end LocalGL2
p2m_reactivate "P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.LocalGL2"

open scoped Pointwise
p2m_open "LocalGL2 P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.LocalGL2 HeckePair P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.HeckePair"

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀] (k : ℕ)
    (hk2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 2)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hk3 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 3)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hSk : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)}) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) hk2
      = (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 3)) hk3 : HeckeAlgebra (integralSubgroup R K) R₀)
        + (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀)
          • heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) hSk := by
  apply LocalGL2.heckeIndicator_diagPi_mul_localRepInf_pow_impl <;> assumption

end S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow
end P2MW
export P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow (solution)
