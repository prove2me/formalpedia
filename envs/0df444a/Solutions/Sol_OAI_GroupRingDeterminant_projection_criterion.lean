-- Prove2me | solution 1 for OAI.GroupRingDeterminant.projection_criterion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:04:27.721005+00:00
-- url     : https://prove2.me/submissions/8ceab626-98f9-4e72-a527-ed3c4c6cda6d

import Mathlib
import Definitions.Def_GroupRingDeterminant
import Definitions.Def_OAIQWGRD000

section
-- module Solutions.OAIQW_GroupRingDeterminant.Defects
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR ud ul um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

theorem fkDet_pos {G : Type} [Group G] {n : ℕ}
    (T : Hilbert G n →L[ℂ] Hilbert G n) : 0 < fkDet T :=
  Real.exp_pos _

section CornerLifting
variable {R : Type uR} [Ring R]

theorem cornerSeries_spec (e z : R) (he : e * e = e)
    (hez : e * z = z) (hze : z * e = z) (k : ℕ) (hk : (e - z) ^ k = 0) :
    cornerSeries e z k * z = e ∧ z * cornerSeries e z k = e ∧
      e * cornerSeries e z k = cornerSeries e z k ∧
      cornerSeries e z k * e = cornerSeries e z k := by
  let w := e - z
  let s := ∑ i ∈ Finset.range k, w ^ i
  have hew : e * w = w := by simp only [w, mul_sub, he, hez]
  have hwe : w * e = w := by simp only [w, sub_mul, he, hze]
  have hew' : Commute e w := hew.trans hwe.symm
  have hes : Commute e s :=
    Commute.sum_right _ _ _ (fun i _ => hew'.pow_right i)
  have hz : z = e * (1 - w) := by simp only [mul_sub, mul_one, hew, w]; noncomm_ring
  have hinv : s * (1 - w) = 1 := by
    simpa only [w, hk, sub_zero] using geom_sum_mul_neg w k
  have hinv' : (1 - w) * s = 1 := by
    simpa only [w, hk, sub_zero] using mul_neg_geom_sum w k
  change (e * s) * z = e ∧ z * (e * s) = e ∧
    e * (e * s) = e * s ∧ (e * s) * e = e * s
  have hq : (e * s) * e = e * s := by
    rw [mul_assoc, ← hes.eq, ← mul_assoc, he]
  refine ⟨?_, ?_, ?_, hq⟩
  · rw [hz, ← mul_assoc, hq, mul_assoc, hinv, mul_one]
  · calc
      z * (e * s) = z * s := by rw [← mul_assoc, hze]
      _ = e := by rw [hz, mul_assoc, hinv', mul_one]
  · rw [← mul_assoc, he]

theorem lift_rectangular_factorization {m : Type um} {r : Type ur} [Fintype m] [DecidableEq m]
    [Fintype r] (e : Matrix m m R) (he : e * e = e)
    (u₀ : Matrix m r R) (v₀ : Matrix r m R) (k : ℕ)
    (hk : (e - e * u₀ * v₀ * e) ^ k = 0) :
    ∃ u : Matrix m r R, ∃ v : Matrix r m R, u * v = e := by
  let z := e * u₀ * v₀ * e
  have hez : e * z = z := by
    dsimp [z]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, he]
  have hze : z * e = z := by
    dsimp [z]
    rw [Matrix.mul_assoc (e * u₀ * v₀), he]
  obtain ⟨hqz, _, _, _⟩ := cornerSeries_spec e z he hez hze k hk
  refine ⟨cornerSeries e z k * e * u₀, v₀ * e, ?_⟩
  simpa only [z, Matrix.mul_assoc] using hqz

end CornerLifting

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ModularLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uA um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ModularKernel
variable (k : ℕ) (hk : 0 < k)

theorem kernel_reduceTwo (a : ZMod (2 ^ k)) (ha : reduceTwo k hk a = 0) :
    a = 2 * (a.val / 2 : ℕ) := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  have hv : (a.val : ZMod 2) = 0 := by
    rw [← map_natCast (reduceTwo k hk), ZMod.natCast_zmod_val]
    exact ha
  have hd : 2 ∣ a.val := (ZMod.natCast_eq_zero_iff _ _).mp hv
  calc
    a = (a.val : ZMod (2 ^ k)) := (ZMod.natCast_zmod_val a).symm
    _ = ((2 * (a.val / 2) : ℕ) : ZMod (2 ^ k)) := by rw [Nat.mul_div_cancel' hd]
    _ = _ := by push_cast; rfl

variable {G : Type uG} [Group G]

theorem kernel_reduceGroupTwo (a : MonoidAlgebra (ZMod (2 ^ k)) G)
    (ha : reduceGroupTwo k hk a = 0) : a = 2 * halfGroup k a := by
  apply MonoidAlgebra.ext
  ext g
  have hg := congrArg (fun c : MonoidAlgebra (ZMod 2) G => c.coeff g) ha
  have hc : reduceTwo k hk (a.coeff g) = 0 := by
    simpa only [reduceGroupTwo, MonoidAlgebra.coeff_mapRingHom,
      MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hg
  simpa [two_mul, halfGroup, MonoidAlgebra.coeff_add] using kernel_reduceTwo k hk _ hc

theorem twice_pow_eq_zero {A : Type uA} [Ring A] [Algebra (ZMod (2 ^ k)) A] (v : A) :
    (2 * v) ^ k = 0 := by
  have htwo : (2 : ZMod (2 ^ k)) ^ k = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2 ^ k)
  have ht : (2 : A) ^ k = 0 := by
    simpa only [map_pow, map_ofNat, map_zero] using
      congrArg (algebraMap (ZMod (2 ^ k)) A) htwo
  have hc : Commute (2 : A) v := by
    simpa only [Nat.cast_ofNat] using Nat.cast_commute 2 v
  rw [hc.mul_pow, ht, zero_mul]

theorem matrix_kernel_nilpotent {m : Type um} [Fintype m] [DecidableEq m]
    (W : Matrix m m (MonoidAlgebra (ZMod (2 ^ k)) G))
    (hW : W.map (reduceGroupTwo k hk) = 0) : W ^ k = 0 := by
  let V : Matrix m m (MonoidAlgebra (ZMod (2 ^ k)) G) := fun i j => halfGroup k (W i j)
  have hv : W = 2 * V := by
    rw [two_mul]
    apply Matrix.ext
    intro i j
    have hc : reduceGroupTwo k hk (W i j) = 0 := congrFun (congrFun hW i) j
    change W i j = halfGroup k (W i j) + halfGroup k (W i j)
    simpa only [two_mul] using kernel_reduceGroupTwo k hk _ hc
  rw [hv]
  exact twice_pow_eq_zero k V

theorem reduceGroupTwo_surjective :
    Function.Surjective (reduceGroupTwo k hk (G := G)) :=
  MonoidAlgebra.map_surjective _ (ZMod.castHom_surjective (dvd_pow_self 2 (Nat.ne_of_gt hk)))

theorem integerReduction_surjective (q : ℕ) : Function.Surjective
    (MonoidAlgebra.mapRingHom G (Int.castRingHom (ZMod q))) :=
  MonoidAlgebra.map_surjective _ ZMod.intCast_surjective

end ModularKernel

section ModularFactorization
variable {G : Type uG} {m : Type um} {r : Type ur} [Group G] [Fintype m] [DecidableEq m] [Fintype r]

theorem lift_binary_factorization (k : ℕ) (hk : 0 < k)
    (e : Matrix m m (MonoidAlgebra (ZMod (2 ^ k)) G)) (he : e * e = e)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G))
    (huv : u * v = e.map (reduceGroupTwo k hk)) :
    ∃ u' : Matrix m r (MonoidAlgebra (ZMod (2 ^ k)) G),
    ∃ v' : Matrix r m (MonoidAlgebra (ZMod (2 ^ k)) G), u' * v' = e := by
  classical
  have hs := reduceGroupTwo_surjective (G := G) k hk
  choose uRaw hu₀ using fun i j => hs (u i j)
  choose vRaw hv₀ using fun i j => hs (v i j)
  let u₀ : Matrix m r (MonoidAlgebra (ZMod (2 ^ k)) G) := uRaw
  let v₀ : Matrix r m (MonoidAlgebra (ZMod (2 ^ k)) G) := vRaw
  have hu : Matrix.map u₀ (reduceGroupTwo k hk) = u := Matrix.ext hu₀
  have hv : Matrix.map v₀ (reduceGroupTwo k hk) = v := Matrix.ext hv₀
  apply lift_rectangular_factorization e he u₀ v₀ k
  apply matrix_kernel_nilpotent k hk
  rw [Matrix.map_sub _ (map_sub _) _ _]
  simp only [Matrix.map_mul, hu, hv]
  rw [Matrix.mul_assoc (e.map _) u, huv]
  have he' : e.map (reduceGroupTwo k hk) * e.map (reduceGroupTwo k hk) =
      e.map (reduceGroupTwo k hk) := by rw [← Matrix.map_mul, he]
  rw [he', he', sub_self]

end ModularFactorization

theorem exists_binary_modulus (D : ℕ) (hD : 0 < D) (hodd : Odd D) :
    ∃ k : ℕ, 0 < k ∧ 1 < 2 ^ k ∧ Nat.ModEq D (2 ^ k) 1 := by
  have hk : 0 < D.totient := Nat.totient_pos.mpr hD
  refine ⟨D.totient, hk, one_lt_pow₀ (by decide) (Nat.ne_of_gt hk), ?_⟩
  exact Nat.ModEq.pow_totient (Nat.coprime_two_right.mpr hodd).symm

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularAction
open scoped ENNReal
variable {G : Type} [Group G] {n : ℕ}

theorem regularOperator_spec (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    IsRegularOperator A (regularOperator A) := by
  classical
  intro ξ i h
  simp only [regularOperator, Finsupp.sum, sum_apply,
    smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, elementaryOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [Ne.symm hbi]
  · simp

end RegularAction

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.TransferAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uF uR ur um

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section TransferAlgebra
variable {F : Type uF} {R : Type uR} {r : Type ur} {m : Type um} [Field F] [Ring R] [Algebra F R]
variable [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

theorem transferMatrix_factorization (q : F) (hq : q ≠ 0) (P : Matrix m m R)
    (U : Matrix m r R) (V : Matrix r m R) :
    lowerShear (q⁻¹ • U) *
      Matrix.fromBlocks (q • (1 : Matrix r r R)) 0 0
        (projectionReweight P (-q⁻¹) (-1 : F)) * upperShear (q⁻¹ • V) =
      transferMatrix q P U V := by
  rw [lowerShear, upperShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [inv_mul_cancel₀ hq, mul_inv_cancel₀ hq, one_smul]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp
  · simp only [projectionReweight, neg_smul, one_smul, smul_sub, smul_smul,
      inv_mul_cancel₀ hq, mul_one, one_smul]
    abel

theorem transferMatrix_isUnit (q : F) (hq : q ≠ 0) (P : Matrix m m R)
    (hP : P * P = P) (U : Matrix m r R) (V : Matrix r m R) :
    IsUnit (transferMatrix q P U V) := by
  have hu : IsUnit (q • (1 : Matrix r r R)) := by
    rw [Algebra.smul_def, mul_one]
    exact (isUnit_iff_ne_zero.mpr hq).map (algebraMap F (Matrix r r R))
  obtain ⟨a, ha⟩ := hu
  let b := projectionReweightUnit P hP (-q⁻¹) (-1 : F)
    (neg_ne_zero.mpr (inv_ne_zero hq)) (neg_ne_zero.mpr one_ne_zero)
  rw [← transferMatrix_factorization q hq P U V]
  have hd : IsUnit (Matrix.fromBlocks (q • (1 : Matrix r r R)) 0 0
      (projectionReweight P (-q⁻¹) (-1 : F))) := by
    refine ⟨blockDiagonalUnit a b, ?_⟩
    change Matrix.fromBlocks (a : Matrix r r R) 0 0
      (projectionReweight P (-q⁻¹) (-1 : F)) = _
    rw [ha]
  exact (lowerShearUnit (q⁻¹ • U)).isUnit.mul hd |>.mul (upperShearUnit (q⁻¹ • V)).isUnit

end TransferAlgebra

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.RegularTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularTrace
variable {G : Type} [Group G] {n : ℕ}

theorem identityVector_apply [DecidableEq G] (i j : Fin n) (g : G) :
    identityVector i (j, g) = if j = i ∧ g = 1 then 1 else 0 := by
  classical
  simp only [identityVector, lp.single_apply, Pi.single_apply, Prod.mk.injEq]

end RegularTrace

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.IntegralTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section IntegralTransfer
variable {G : Type uG} {m : Type um} {r : Type ur} [Group G] [Fintype m] [DecidableEq m]
  [Fintype r] [DecidableEq r]

theorem kernel_integerReduction (q : ℕ) (a : MonoidAlgebra ℤ G)
    (ha : MonoidAlgebra.mapRingHom G (Int.castRingHom (ZMod q)) a = 0) :
    (q : ℤ) • divideGroup q a = a := by
  apply MonoidAlgebra.ext
  ext g
  have hg := congrArg (fun x : MonoidAlgebra (ZMod q) G => x.coeff g) ha
  change (a.coeff g : ZMod q) = 0 at hg
  have hd : (q : ℤ) ∣ a.coeff g := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by
    simpa only [MonoidAlgebra.coeff_mapRingHom,
      MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hg)
  rw [MonoidAlgebra.coeff_smul]
  change (q : ℤ) * (a.coeff g / (q : ℤ)) = a.coeff g
  exact Int.mul_ediv_cancel' hd

omit [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem map_toRat_zsmul (t : ℤ) (A : Matrix m r (MonoidAlgebra ℤ G)) :
    (t • A).map toRat = (t : ℚ) • A.map toRat := by
  rw [Int.cast_smul_eq_zsmul]
  exact Matrix.map_smul _ _ (fun a => map_zsmul toRat _ a) _

theorem integral_transfer_of_lifts (q : ℕ) (hq : q ≠ 0)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P)
    (C : Matrix m m (MonoidAlgebra ℤ G))
    (hC : C.map toRat = P + (q : ℚ) • (1 - P))
    (U : Matrix m r (MonoidAlgebra ℤ G)) (V : Matrix r m (MonoidAlgebra ℤ G))
    (huv : (U * V).map (toMod q) = C.map (toMod q)) :
    ∃ A : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℤ G),
      A.map toRat = transferMatrix (q : ℚ) P (U.map toRat) (V.map toRat) ∧
      IsUnit (A.map toRat) := by
  let W : Matrix m m (MonoidAlgebra ℤ G) := fun i j => divideGroup q ((U * V - C) i j)
  have hw : (q : ℤ) • W = U * V - C := by
    apply Matrix.ext
    intro i j
    apply kernel_integerReduction
    have h := congrFun (congrFun huv i) j
    change toMod q ((U * V) i j - C i j) = 0
    rw [map_sub, sub_eq_zero]
    exact h
  have hwq := congrArg (fun A : Matrix m m (MonoidAlgebra ℤ G) => A.map toRat) hw
  rw [map_toRat_zsmul, Int.cast_natCast, Matrix.map_sub _ (map_sub _) _ _, Matrix.map_mul, hC] at hwq
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hw' : W.map toRat = (q : ℚ)⁻¹ •
      (U.map toRat * V.map toRat - P - (q : ℚ) • (1 - P)) := by
    rw [sub_sub, ← hwq, smul_smul, inv_mul_cancel₀ hq', one_smul]
  refine ⟨Matrix.fromBlocks ((q : ℤ) • 1) V U W, ?_, ?_⟩
  · rw [Matrix.fromBlocks_map, map_toRat_zsmul,
      Int.cast_natCast, Matrix.map_one _ (map_zero _) (map_one _), hw']
    rfl
  · rw [Matrix.fromBlocks_map, map_toRat_zsmul,
      Int.cast_natCast, Matrix.map_one _ (map_zero _) (map_one _), hw']
    exact transferMatrix_isUnit (q : ℚ) hq' P hP (U.map toRat) (V.map toRat)

omit [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem map_toMod_zsmul (q : ℕ) (t : ℤ) (A : Matrix m r (MonoidAlgebra ℤ G)) :
    (t • A).map (toMod q) = (t : ZMod q) • A.map (toMod q) := by
  rw [Int.cast_smul_eq_zsmul]
  exact Matrix.map_smul _ _ (fun a => map_zsmul (toMod q) _ a) _

omit [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem reduceGroupTwo_toMod (k : ℕ) (hk : 0 < k) (a : MonoidAlgebra ℤ G) :
    reduceGroupTwo k hk (toMod (2 ^ k) a) = toMod 2 a := by
  apply MonoidAlgebra.ext
  ext g
  simp only [reduceGroupTwo, toMod, MonoidAlgebra.coeff_mapRingHom]
  exact map_intCast (reduceTwo k hk) _

omit [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem integer_projection_square (P : Matrix m m (MonoidAlgebra ℚ G))
    (hP : P * P = P) (D : ℤ) (Z : Matrix m m (MonoidAlgebra ℤ G))
    (hZ : Z.map toRat = (D : ℚ) • P) : Z * Z = D • Z := by
  have hi : Function.Injective (toRat (G := G)) :=
    MonoidAlgebra.map_injective (Int.castRingHom ℚ).toAddMonoidHom Int.cast_injective
  apply Matrix.map_injective hi
  change (Z * Z).map toRat = (D • Z).map toRat
  rw [Matrix.map_mul, map_toRat_zsmul, hZ, Matrix.smul_mul, Matrix.mul_smul, hP]

omit [Fintype r] [DecidableEq r] in

theorem integral_reweight_mod_idempotent (q : ℕ) (D t : ℤ)
    (hDt : D * t = 1 - (q : ℤ)) (Z : Matrix m m (MonoidAlgebra ℤ G))
    (hZ : Z * Z = D • Z) :
    let C := (q : ℤ) • (1 : Matrix m m (MonoidAlgebra ℤ G)) + t • Z
    C.map (toMod q) * C.map (toMod q) = C.map (toMod q) := by
  dsimp only
  have hqt : ((q : ℤ) : ZMod q) = 0 := by simp
  have hdt : (D : ZMod q) * (t : ZMod q) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) hDt
    simpa using h
  have hzz : Z.map (toMod q) * Z.map (toMod q) = (D : ZMod q) • Z.map (toMod q) := by
    rw [← Matrix.map_mul, hZ, map_toMod_zsmul]
  simp only [Matrix.map_add _ (map_add _) _ _, map_toMod_zsmul, hqt,
    zero_smul, zero_add]
  rw [Matrix.smul_mul, Matrix.mul_smul, hzz, smul_smul, smul_smul]
  congr 1
  calc
    (t : ZMod q) * (t : ZMod q) * (D : ZMod q) = (t : ZMod q) * ((D : ZMod q) * t) := by ring
    _ = (t : ZMod q) := by rw [hdt, mul_one]

omit [Fintype m] [Fintype r] [DecidableEq r] in
theorem integral_reweight_rational (q : ℕ) (D t : ℤ)
    (hDt : D * t = 1 - (q : ℤ)) (Z : Matrix m m (MonoidAlgebra ℤ G))
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hZ : Z.map toRat = (D : ℚ) • P) :
    ((q : ℤ) • (1 : Matrix m m (MonoidAlgebra ℤ G)) + t • Z).map toRat =
      P + (q : ℚ) • (1 - P) := by
  have hdt : (t : ℚ) * (D : ℚ) = 1 - (q : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hDt
    simpa [mul_comm] using h
  rw [Matrix.map_add _ (map_add _) _ _, map_toRat_zsmul, map_toRat_zsmul,
    Matrix.map_one _ (map_zero _) (map_one _), hZ, smul_smul, hdt]
  simp only [Int.cast_natCast, sub_smul, one_smul, smul_sub]
  abel

theorem integral_transfer (D : ℕ) (hodd : Odd D)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P)
    (Z : Matrix m m (MonoidAlgebra ℤ G)) (hZ : Z.map toRat = (D : ℚ) • P)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G)) (huv : u * v = Z.map (toMod 2))
    (k : ℕ) (hk : 0 < k) (t : ℤ) (hDt : (D : ℤ) * t = 1 - (2 ^ k : ℕ)) :
    ∃ (U : Matrix m r (MonoidAlgebra ℤ G)) (V : Matrix r m (MonoidAlgebra ℤ G))
      (A : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℤ G)),
      A.map toRat = transferMatrix ((2 ^ k : ℕ) : ℚ) P (U.map toRat) (V.map toRat) ∧
      IsUnit (A.map toRat) := by
  classical
  let q : ℕ := 2 ^ k
  let C : Matrix m m (MonoidAlgebra ℤ G) := (q : ℤ) • 1 + t • Z
  let e : Matrix m m (MonoidAlgebra (ZMod q) G) := C.map (toMod q)
  have hZZ : Z * Z = (D : ℤ) • Z :=
    integer_projection_square P hP D Z (by simpa using hZ)
  have he : e * e = e := integral_reweight_mod_idempotent q D t hDt Z hZZ
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hD2 : (D : ZMod 2) = 1 := by
    obtain ⟨a, rfl⟩ := hodd
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, htwo, zero_mul,
      zero_add, Nat.cast_one]
  have hq2 : (q : ZMod 2) = 0 := by
    simp only [q, Nat.cast_pow, Nat.cast_ofNat, htwo, zero_pow hk.ne']
  have ht2 : (t : ZMod 2) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) hDt
    push_cast at h
    simpa only [hD2, htwo, zero_pow hk.ne', one_mul, sub_zero] using h
  have hC2 : C.map (toMod 2) = Z.map (toMod 2) := by
    simp only [C, Matrix.map_add _ (map_add _) _ _, map_toMod_zsmul,
      Int.cast_natCast, hq2, ht2, zero_smul, one_smul, zero_add]
  have he2 : e.map (reduceGroupTwo k hk) = C.map (toMod 2) := by
    apply Matrix.ext
    intro i j
    exact reduceGroupTwo_toMod k hk (C i j)
  obtain ⟨u', v', hu'v'⟩ := lift_binary_factorization k hk e he u v (by
    rw [he2, hC2]
    exact huv)
  have hs := integerReduction_surjective (G := G) q
  choose U₀ hU₀ using fun i j => hs (u' i j)
  choose V₀ hV₀ using fun i j => hs (v' i j)
  let U : Matrix m r (MonoidAlgebra ℤ G) := U₀
  let V : Matrix r m (MonoidAlgebra ℤ G) := V₀
  have hU : U.map (toMod q) = u' := Matrix.ext hU₀
  have hV : V.map (toMod q) = v' := Matrix.ext hV₀
  have hUV : (U * V).map (toMod q) = C.map (toMod q) := by
    rw [Matrix.map_mul, hU, hV, hu'v']
  have hC : C.map toRat = P + (q : ℚ) • (1 - P) :=
    integral_reweight_rational q D t hDt Z P (by simpa using hZ)
  obtain ⟨A, ha, haunit⟩ := integral_transfer_of_lifts q
    (pow_ne_zero _ (by decide)) P hP C hC U V hUV
  exact ⟨U, V, A, ha, haunit⟩

theorem integral_transfer_of_congruence (D : ℕ) (hodd : Odd D)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P)
    (Z : Matrix m m (MonoidAlgebra ℤ G)) (hZ : Z.map toRat = (D : ℚ) • P)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G)) (huv : u * v = Z.map (toMod 2))
    (k : ℕ) (hk : 0 < k) (hkD : Nat.ModEq D (2 ^ k) 1) :
    ∃ (U : Matrix m r (MonoidAlgebra ℤ G)) (V : Matrix r m (MonoidAlgebra ℤ G))
      (A : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℤ G)),
      A.map toRat = transferMatrix ((2 ^ k : ℕ) : ℚ) P (U.map toRat) (V.map toRat) ∧
      IsUnit (A.map toRat) := by
  obtain ⟨t, ht⟩ := Nat.modEq_iff_dvd.mp hkD
  exact integral_transfer D hodd P hP Z hZ u v huv k hk t (by simpa using ht.symm)

end IntegralTransfer

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ComplexRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ComplexRegular
variable {G : Type} [Group G] {n : ℕ}

open scoped Matrix.Module

attribute [local instance] OAI.GroupRingDeterminant.functionModule
theorem complexOperator_isUnit {A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)}
    (hA : IsUnit A) : IsUnit (complexOperator A) := hA.map complexRepresentation

theorem complexOperator_integer (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    complexOperator (A.map (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ))) =
      regularOperator A := by
  classical
  unfold complexOperator regularOperator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (MonoidAlgebra.map (Int.castRingHom ℂ).toAddMonoidHom (A i j)).coeff.sum _ = _
  rw [MonoidAlgebra.coeff_map]
  exact Finsupp.sum_mapRange_index
    (h := fun groupElement coefficient => coefficient • elementaryOperator i j groupElement)
    (fun groupElement => zero_smul ℂ (elementaryOperator i j groupElement))

theorem regularOperator_isUnit {A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)}
    (hA : IsUnit (rationalMatrix A)) : IsUnit (regularOperator A) := by
  let f : MonoidAlgebra ℚ G →+* MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapRingHom G (Rat.castHom ℂ)
  have h := complexOperator_isUnit (hA.map f.mapMatrix)
  have hf : f.comp (MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ)) =
      MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) := by
    rw [← MonoidAlgebra.mapRingHom_comp]
    congr 1
  change IsUnit (complexOperator (A.map
    (f.comp (MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ))))) at h
  rw [hf, complexOperator_integer] at h
  exact h

theorem groupTraceCLM_apply (T : Hilbert G n →L[ℂ] Hilbert G n) :
    groupTraceCLM T = groupTrace T := by
  simp [groupTraceCLM, groupTrace]

theorem groupTrace_complex (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    groupTrace (complexOperator A) = ∑ i : Fin n, (A i i).coeff 1 := by
  classical
  unfold groupTrace
  apply Finset.sum_congr rfl
  intro i _
  have hi (ξ : Hilbert G n) : inner ℂ (identityVector i) ξ = ξ (i, 1) := by
    simp [identityVector, lp.inner_single_left, RCLike.inner_apply]
  rw [hi, complexOperator_apply]
  rw [Finset.sum_eq_single i]
  · rw [(A i i).coeff.sum_eq_single 1]
    · simp [identityVector_apply]
    · intro g _ hg
      simp [identityVector_apply, hg]
    · simp
  · intro j _ hji
    simp [identityVector_apply, hji]
  · simp

theorem coefficient_mul_comm (a b : MonoidAlgebra ℂ G) :
    (a * b).coeff 1 = (b * a).coeff 1 := by
  rw [MonoidAlgebra.coeff_mul_apply_left a b, MonoidAlgebra.coeff_mul_apply_right b a]
  simp only [mul_one, one_mul, mul_comm]

theorem groupTrace_complex_mul_comm
    (A B : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    groupTrace (complexOperator A * complexOperator B) =
      groupTrace (complexOperator B * complexOperator A) := by
  classical
  rw [← complexOperator_mul, ← complexOperator_mul, groupTrace_complex, groupTrace_complex]
  simp only [Matrix.mul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact coefficient_mul_comm _ _

end ComplexRegular

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.RegularAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularStar
variable {G : Type} [Group G] {n : ℕ}

theorem groupTrace_star (T : Hilbert G n →L[ℂ] Hilbert G n) :
    groupTrace (star T) = star (groupTrace T) := by
  simp only [groupTrace, star_sum, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  apply Finset.sum_congr rfl
  intro i _
  exact (inner_conj_symm (T (identityVector i)) (identityVector i)).symm

end RegularStar

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ClosedAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section GroupAlgebraClosure
variable {G : Type} [Group G] {n : ℕ}

theorem continuous_groupTrace : Continuous (groupTrace (G := G) (n := n)) := by
  have he : (fun T => groupTraceCLM (G := G) (n := n) T) = groupTrace :=
    funext groupTraceCLM_apply
  rw [← he]
  exact groupTraceCLM.continuous

theorem groupTrace_closed_mul_comm {S T : Hilbert G n →L[ℂ] Hilbert G n}
    (hS : S ∈ closedGroupAlgebra) (hT : T ∈ closedGroupAlgebra) :
    groupTrace (S * T) = groupTrace (T * S) := by
  have hfinite {X Y : Hilbert G n →L[ℂ] Hilbert G n}
      (hX : X ∈ finiteGroupStarAlgebra) (hY : Y ∈ finiteGroupStarAlgebra) :
      groupTrace (X * Y) = groupTrace (Y * X) := by
    obtain ⟨A, rfl⟩ := hX
    obtain ⟨B, rfl⟩ := hY
    exact groupTrace_complex_mul_comm A B
  have hleft {X Y : Hilbert G n →L[ℂ] Hilbert G n}
      (hX : X ∈ finiteGroupStarAlgebra) (hY : Y ∈ closedGroupAlgebra) :
      groupTrace (X * Y) = groupTrace (Y * X) := by
    apply closure_minimal (fun Z hZ => hfinite hX hZ)
      (isClosed_eq (continuous_groupTrace.comp (continuous_const.mul continuous_id))
        (continuous_groupTrace.comp (continuous_id.mul continuous_const))) hY
  exact closure_minimal (fun X hX => hleft hX hT)
    (isClosed_eq (continuous_groupTrace.comp (continuous_id.mul continuous_const))
      (continuous_groupTrace.comp (continuous_const.mul continuous_id))) hS

end GroupAlgebraClosure

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.LogSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology
section Analysis
variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A]

lemma trace_power_derivative (τ : A →L[ℝ] ℂ) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (a b : A) (n : ℕ) :
    τ (∑ i ∈ Finset.range (n + 1), a ^ (n - i) * b * a ^ i) =
      (n + 1 : ℝ) • τ (b * a ^ n) := by
  rw [map_sum]
  have hh (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      τ (a ^ (n - i) * b * a ^ i) = τ (b * a ^ n) := by
    rw [mul_assoc, hτ, mul_assoc, ← pow_add]
    rw [Nat.add_sub_of_le]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp_rw [Finset.sum_congr rfl hh]
  simp [← Nat.cast_smul_eq_nsmul ℝ]

lemma hasDerivAt_trace_pow_div (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f : ℝ → A} {f' : A} {x : ℝ} (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun y => τ ((n + 1 : ℝ)⁻¹ • f y ^ (n + 1)))
      (τ (f' * f x ^ n)) x := by
  have h := τ.hasFDerivAt.comp_hasDerivAt x ((hf.fun_pow' (n + 1)).const_smul (n + 1 : ℝ)⁻¹)
  simpa only [Function.comp_def, Pi.smul_def, map_smul, Nat.pred_succ,
    trace_power_derivative τ hτ, smul_smul,
    inv_mul_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity), one_smul] using h

section Complete
variable [CompleteSpace A] [NormOneClass A]

lemma summable_trace_pow_div (τ : A →L[ℝ] ℂ) (a : A) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => τ ((n + 1 : ℝ)⁻¹ • a ^ (n + 1))) := by
  have hs : Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹ • a ^ (n + 1)) := by
    apply Summable.of_norm_bounded (g := fun n => ‖a‖ ^ (n + 1))
    · simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right ‖a‖
    · intro n
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact (mul_le_mul_of_nonneg_left (norm_pow_le a (n + 1)) (by positivity)).trans
        (mul_le_of_le_one_left (by positivity)
          (inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))
  exact τ.summable hs

lemma hasDerivAt_trace_logSeries (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f f' : ℝ → A} {s : Set ℝ} {x ρ B : ℝ}
    (hs : IsOpen s) (hsc : IsPreconnected s) (hx : x ∈ s)
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y)
    (hρ : ρ < 1) (hρ₀ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hn : ∀ y ∈ s, ‖f y‖ ≤ ρ) (hn' : ∀ y ∈ s, ‖f' y‖ ≤ B) :
    HasDerivAt (fun y => ∑' n : ℕ, τ ((n + 1 : ℝ)⁻¹ • f y ^ (n + 1)))
      (τ (f' x * Ring.inverse (1 - f x))) x := by
  have hsum : HasSum (fun n : ℕ => τ (f' x * f x ^ n))
      (τ (f' x * Ring.inverse (1 - f x))) := by
    exact τ.hasSum ((hasSum_geom_series_inverse (f x) ((hn x hx).trans_lt hρ)).mul_left (f' x))
  have hd := hasDerivAt_tsum_of_isPreconnected
    ((summable_geometric_of_lt_one hρ₀ hρ).mul_left (‖τ‖ * B)) hs hsc
    (fun n y hy => hasDerivAt_trace_pow_div τ hτ (hf y hy) n)
    (fun n y hy => show ‖τ (f' y * f y ^ n)‖ ≤ ‖τ‖ * B * ρ ^ n from
      (τ.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_mul (hn' y hy)
          ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hn y hy) n))
          (by positivity) hB)) (norm_nonneg _)).trans (le_of_eq (mul_assoc _ _ _).symm)))
    hx (summable_trace_pow_div τ (f x) ((hn x hx).trans_lt hρ)) hx
  rwa [hsum.tsum_eq] at hd

lemma hasDerivAt_trace_logSeries_local (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f f' : ℝ → A} {x : ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hc : ContinuousAt f' x) (hn : ‖f x‖ < 1) :
    HasDerivAt (fun y => ∑' n : ℕ, τ ((n + 1 : ℝ)⁻¹ • f y ^ (n + 1)))
      (τ (f' x * Ring.inverse (1 - f x))) x := by
  obtain ⟨ρ, hρx, hρ⟩ := exists_between hn
  let B := ‖f' x‖ + 1
  have he : ∀ᶠ y in 𝓝 x, ‖f y‖ < ρ ∧ ‖f' y‖ < B :=
    ((hf x).continuousAt.norm.eventually (gt_mem_nhds hρx)).and
      (hc.norm.eventually (gt_mem_nhds (show ‖f' x‖ < B by dsimp [B]; linarith)))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  exact hasDerivAt_trace_logSeries τ hτ Metric.isOpen_ball (convex_ball x ε).isPreconnected
    (Metric.mem_ball_self hε) (fun y _ => hf y) hρ ((norm_nonneg _).trans hρx.le)
    (by dsimp [B]; positivity) (fun y hy => (he hy).1.le) (fun y hy => (he hy).2.le)

end Complete

end Analysis
section CFCSeries
variable {A : Type uA} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

omit [StarRing A] [CompleteSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
lemma norm_pow_div_le_geom (W : A) (n : ℕ) :
    ‖(n + 1 : ℝ)⁻¹ • W ^ (n + 1)‖ ≤ ‖W‖ ^ (n + 1) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (norm_pow_le W (n + 1)) (by positivity)).trans
    (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))

omit [StarRing A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
lemma summable_pow_div (W : A) (hW : ‖W‖ < 1) :
    Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹ • W ^ (n + 1)) := by
  apply Summable.of_norm_bounded (g := fun n => ‖W‖ ^ (n + 1))
  · simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg W) hW).mul_right ‖W‖
  · exact norm_pow_div_le_geom W

lemma hasSum_pow_div_cfc_log [Nontrivial A] (W : A) (hW : IsSelfAdjoint W) (hWn : ‖W‖ < 1) :
    HasSum (fun n : ℕ => (n + 1 : ℝ)⁻¹ • W ^ (n + 1)) (-CFC.log (1 - W)) := by
  let : Nonempty (spectrum ℝ W) :=
    (ContinuousFunctionalCalculus.spectrum_nonempty W hW).to_subtype
  let X : C(spectrum ℝ W, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hX : ‖X‖ ≤ ‖W‖ := by
    apply (ContinuousMap.norm_le X (norm_nonneg W)).mpr
    intro x
    exact spectrum.norm_le_norm_of_mem x.property
  have hXs : Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹ • X ^ (n + 1)) :=
    summable_pow_div X (hX.trans_lt hWn)
  have hc : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (spectrum ℝ W) := by
    intro x hx
    have hxn : |x| < 1 := (spectrum.norm_le_norm_of_mem hx).trans_lt hWn
    have hne : 1 - x ≠ 0 := by have := (abs_lt.mp hxn).2; linarith
    exact ((Real.continuousAt_log hne).comp (continuous_const.sub continuous_id).continuousAt).neg.continuousWithinAt
  let L : C(spectrum ℝ W, ℝ) := ⟨fun x => -Real.log (1 - x.1), hc.domRestrict⟩
  have hs : HasSum (fun n : ℕ => (n + 1 : ℝ)⁻¹ • X ^ (n + 1)) L := by
    rw [hXs.hasSum_iff]
    ext x
    rw [← ContinuousMap.tsum_apply hXs]
    have hh := Real.hasSum_pow_div_log_of_abs_lt_one
      ((spectrum.norm_le_norm_of_mem x.property).trans_lt hWn)
    change (∑' n : ℕ, (n + 1 : ℝ)⁻¹ * (x.1) ^ (n + 1)) = -Real.log (1 - x.1)
    simpa [div_eq_mul_inv, mul_comm] using hh.tsum_eq
  have h := (cfcL hW).hasSum hs
  have hterm (n : ℕ) : (cfcL hW) ((n + 1 : ℝ)⁻¹ • X ^ (n + 1)) =
      (n + 1 : ℝ)⁻¹ • W ^ (n + 1) := by
    rw [map_smul]
    congr 1
    change cfcHom hW (X ^ (n + 1)) = _
    rw [map_pow]
    congr 1
    exact (cfc_apply id W hW).symm.trans (cfc_id ℝ W hW)
  have hL : (cfcL hW) L = -CFC.log (1 - W) := by
    change cfcHom hW L = _
    change cfcHom hW ⟨(spectrum ℝ W).domRestrict (fun x : ℝ => -Real.log (1 - x)), _⟩ = _
    rw [← cfc_apply (fun x : ℝ => -Real.log (1 - x)) W hW hc]
    rw [cfc_neg _ W]
    congr 1
    have he : cfc (fun x : ℝ => 1 - x) W = 1 - W := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun x => x) W (by fun_prop) (by fun_prop),
        cfc_const 1 W hW, cfc_id' ℝ W hW, map_one]
    rw [CFC.log, ← he]
    have hc' : ContinuousOn Real.log ((fun x : ℝ => 1 - x) '' spectrum ℝ W) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply (Real.continuousAt_log _).continuousWithinAt
      have hxn : |x| < 1 := (spectrum.norm_le_norm_of_mem hx).trans_lt hWn
      have := (abs_lt.mp hxn).2
      linarith
    rw [← cfc_comp' Real.log (fun x : ℝ => 1 - x) W hc' (by fun_prop) hW]
  simpa only [hterm, hL] using h

end CFCSeries

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.TraceLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section TraceCFC
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

lemma hasDerivAt_trace_log_one_sub (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f f' : ℝ → A} {x : ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hc : ContinuousAt f' x) (hn : ‖f x‖ < 1) (hself : ∀ y, IsSelfAdjoint (f y)) :
    HasDerivAt (fun y => τ (CFC.log (1 - f y)))
      (-τ (f' x * Ring.inverse (1 - f x))) x := by
  have hd := (hasDerivAt_trace_logSeries_local τ hτ hf hc hn).neg
  apply hd.congr_of_eventuallyEq
  have he : ∀ᶠ y in 𝓝 x, ‖f y‖ < 1 :=
    (hf x).continuousAt.norm.eventually (gt_mem_nhds hn)
  filter_upwards [he] with y hy
  have hh := (τ.hasSum (hasSum_pow_div_cfc_log (f y) (hself y) hy)).tsum_eq
  simpa only [map_neg, neg_neg, Pi.neg_apply] using (congrArg Neg.neg hh).symm

omit [Nontrivial A] in
lemma log_smul_of_isUnit (V : A) (hV : IsSelfAdjoint V) (hu : IsUnit V)
    (c : ℝ) (hc : 0 < c) :
    CFC.log (c • V) = Real.log c • (1 : A) + CFC.log V := by
  have hne (x : ℝ) (hx : x ∈ spectrum ℝ V) : x ≠ 0 := by
    intro he
    exact (spectrum.zero_notMem_iff ℝ).mpr hu (he ▸ hx)
  have hl : ContinuousOn Real.log (spectrum ℝ V) := by
    intro x hx
    exact (Real.continuousAt_log (hne x hx)).continuousWithinAt
  have hlc : ContinuousOn Real.log ((fun x : ℝ => c * x) '' spectrum ℝ V) := by
    rintro y ⟨x, hx, rfl⟩
    exact (Real.continuousAt_log (mul_ne_zero hc.ne' (hne x hx))).continuousWithinAt
  have he : cfc (fun x : ℝ => c * x) V = c • V := cfc_const_mul_id c V hV
  rw [CFC.log, ← he, ← cfc_comp' Real.log (fun x : ℝ => c * x) V hlc (by fun_prop) hV]
  calc
    cfc (fun x : ℝ => Real.log (c * x)) V =
        cfc (fun x : ℝ => Real.log c + Real.log x) V := by
      apply cfc_congr
      intro x hx
      exact Real.log_mul hc.ne' (hne x hx)
    _ = Real.log c • (1 : A) + CFC.log V := by
      rw [cfc_add V (fun _ : ℝ => Real.log c) Real.log (by fun_prop) hl,
        cfc_const (Real.log c) V hV, Algebra.algebraMap_eq_smul_one]
      rfl

lemma norm_one_sub_rescale_star_mul_self (M : A) (hu : IsUnit M) :
    ‖1 - (‖star M * M‖ + 1)⁻¹ • (star M * M)‖ < 1 := by
  let N := star M * M
  let c := ‖N‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hN : IsSelfAdjoint N := IsSelfAdjoint.star_mul_self M
  have huN : IsUnit N := hu.star.mul hu
  have he : cfc (fun x : ℝ => 1 - c⁻¹ * x) N = 1 - c⁻¹ • N := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x => c⁻¹ * x) N (by fun_prop) (by fun_prop),
      cfc_const_one ℝ N hN, cfc_const_mul_id c⁻¹ N hN]
  change ‖1 - c⁻¹ • N‖ < 1
  rw [← he]
  apply norm_cfc_lt zero_lt_one
  intro x hx
  have hx₀ : 0 < x := by
    have hn : 0 ≤ x := spectrum_star_mul_self_nonneg x hx
    have hnz : x ≠ 0 := fun hz => (spectrum.zero_notMem_iff ℝ).mpr huN (hz ▸ hx)
    exact lt_of_le_of_ne hn (Ne.symm hnz)
  have hxn : x < c := by
    have hb := spectrum.norm_le_norm_of_mem hx
    dsimp [c]
    rw [Real.norm_of_nonneg hx₀.le] at hb
    linarith
  rw [Real.norm_eq_abs, abs_lt]
  have hxc : 0 < c⁻¹ * x := mul_pos (inv_pos.mpr hc) hx₀
  have hxc' : c⁻¹ * x < 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_one hc).mpr hxn
  constructor <;> linarith

omit [Nontrivial A] in
lemma ringInverse_smul (N : A) (hu : IsUnit N) (c : ℝ) (hc : c ≠ 0) :
    Ring.inverse (c • N) = c⁻¹ • Ring.inverse N := by
  have hu' : IsUnit (c • N) := by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ A)).mul hu
  have hm : (c • N) * (c⁻¹ • Ring.inverse N) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, Ring.mul_inverse_cancel N hu]
  calc
    Ring.inverse (c • N) = Ring.inverse (c • N) * 1 := (mul_one _).symm
    _ = Ring.inverse (c • N) * ((c • N) * (c⁻¹ • Ring.inverse N)) := by rw [hm]
    _ = c⁻¹ • Ring.inverse N := Ring.inverse_mul_cancel_left _ _ hu'

lemma hasDerivAt_trace_log_of_rescale (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {N N' : ℝ → A} {x c : ℝ} (hc : 0 < c)
    (hd : ∀ y, HasDerivAt N (N' y) y) (hdc : ContinuousAt N' x)
    (hself : ∀ y, IsSelfAdjoint (N y)) (hu : ∀ y, IsUnit (N y))
    (hn : ‖1 - c⁻¹ • N x‖ < 1) :
    HasDerivAt (fun y => τ (CFC.log (N y)))
      (τ (N' x * Ring.inverse (N x))) x := by
  let W := fun y => (1 : A) - c⁻¹ • N y
  let W' := fun y => -(c⁻¹ • N' y)
  have hW (y : ℝ) : HasDerivAt W (W' y) y := by
    simpa [W, W'] using (hd y).const_smul c⁻¹ |>.const_sub 1
  have hWc : ContinuousAt W' x := (hdc.const_smul c⁻¹).neg
  have hWs (y : ℝ) : IsSelfAdjoint (W y) :=
    (IsSelfAdjoint.one A).sub ((IsSelfAdjoint.all (c⁻¹)).smul (hself y))
  have he (y : ℝ) : 1 - W y = c⁻¹ • N y := by dsimp [W]; abel
  have hue (y : ℝ) : IsUnit (1 - W y) := by
    rw [he, Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hc.ne')).map (algebraMap ℝ A)).mul (hu y)
  have hrescale (y : ℝ) : c • (1 - W y) = N y := by
    rw [he, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hlog (y : ℝ) : CFC.log (N y) = Real.log c • (1 : A) + CFC.log (1 - W y) := by
    rw [← hrescale y]
    exact log_smul_of_isUnit (1 - W y) ((IsSelfAdjoint.one A).sub (hWs y)) (hue y) c hc
  have H := (hasDerivAt_trace_log_one_sub τ hτ hW hWc hn hWs).const_add
    (τ (Real.log c • (1 : A)))
  have hdval : -τ (W' x * Ring.inverse (1 - W x)) = τ (N' x * Ring.inverse (N x)) := by
    rw [he, ringInverse_smul (N x) (hu x) _ (inv_ne_zero hc.ne'), inv_inv]
    dsimp [W']
    rw [neg_mul, smul_mul_smul_comm, inv_mul_cancel₀ hc.ne', one_smul, map_neg, neg_neg]
  rw [hdval] at H
  convert! H using 1
  ext y
  rw [hlog, map_add]

omit [Nontrivial A] in
lemma trace_star_mul_self_log_derivative_value (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    (M D : A) (hu : IsUnit M) :
    τ ((star D * M + star M * D) * Ring.inverse (star M * M)) =
      (2 * (τ (D * Ring.inverse M)).re : ℝ) := by
  rw [add_mul, map_add]
  have hfirst : τ (star D * M * Ring.inverse (star M * M)) =
      star (τ (D * Ring.inverse M)) := by
    rw [Ring.inverse_mul (Or.inl hu.star), ← mul_assoc,
      Ring.mul_inverse_cancel_right M (star D) hu, hτ, Ring.inverse_star,
      ← star_mul, hstar]
  have hsecond : τ (star M * D * Ring.inverse (star M * M)) = τ (D * Ring.inverse M) := by
    rw [mul_assoc, hτ, Ring.inverse_mul (Or.inl hu.star), mul_assoc D,
      mul_assoc (Ring.inverse M), Ring.inverse_mul_cancel (star M) hu.star, mul_one]
  rw [hfirst, hsecond, add_comm]
  exact Complex.add_conj _

lemma hasDerivAt_trace_log_star_mul_self (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    {M M' : ℝ → A} {x : ℝ} (hd : ∀ y, HasDerivAt M (M' y) y)
    (hdc : ContinuousAt M' x) (hu : ∀ y, IsUnit (M y)) :
    HasDerivAt (fun y => τ (CFC.log (star (M y) * M y)))
      (2 * (τ (M' x * Ring.inverse (M x))).re : ℝ) x := by
  let N := fun y => star (M y) * M y
  let N' := fun y => star (M' y) * M y + star (M y) * M' y
  have hN (y : ℝ) : HasDerivAt N (N' y) y := (hd y).star.mul (hd y)
  have hNc : ContinuousAt N' x :=
    (hdc.star.mul (hd x).continuousAt).add ((hd x).continuousAt.star.mul hdc)
  have H := hasDerivAt_trace_log_of_rescale τ hτ
    (show 0 < ‖N x‖ + 1 by positivity) hN hNc
    (fun y => IsSelfAdjoint.star_mul_self (M y)) (fun y => (hu y).star.mul (hu y))
    (norm_one_sub_rescale_star_mul_self (M x) (hu x))
  rwa [trace_star_mul_self_log_derivative_value τ hτ hstar (M x) (M' x) (hu x)] at H

omit [Nontrivial A] in
lemma trace_derivative_mul_value (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (L R D E : A)
    (hL : IsUnit L) (hR : IsUnit R) :
    τ ((D * R + L * E) * Ring.inverse (L * R)) =
      τ (D * Ring.inverse L) + τ (E * Ring.inverse R) := by
  rw [add_mul, map_add, Ring.inverse_mul (Or.inl hL)]
  congr 1
  · rw [← mul_assoc, Ring.mul_inverse_cancel_right R D hR]
  · rw [mul_assoc L, hτ L, ← mul_assoc E, mul_assoc (E * Ring.inverse R),
      Ring.inverse_mul_cancel L hL, mul_one]

omit [Nontrivial A] in
lemma ringInverse_nilpotentShear (S : A) (hS : S * S = 0) (x : ℝ) :
    Ring.inverse (1 + x • S) = 1 - x • S :=
  Ring.inverse_unit (nilpotentShearUnit S hS x)

omit [Nontrivial A] in
lemma nilpotentShear_trace_derivative (τ : A →L[ℝ] ℂ) (S : A)
    (hS : S * S = 0) (ht : τ S = 0) (x : ℝ) :
    τ (S * Ring.inverse (1 + x • S)) = 0 := by
  rw [ringInverse_nilpotentShear S hS x, mul_sub, mul_one, mul_smul_comm, hS,
    smul_zero, sub_zero, ht]

lemma trace_log_shear_invariant (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    (B S T : A) (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : τ S = 0) (htT : τ T = 0) (x : ℝ) :
    τ (CFC.log (star ((1 + x • S) * B * (1 + x • T)) *
      ((1 + x • S) * B * (1 + x • T)))) = τ (CFC.log (star B * B)) := by
  let M := fun y : ℝ => (1 + y • S) * B * (1 + y • T)
  let M' := fun y : ℝ => S * B * (1 + y • T) + (1 + y • S) * B * T
  have hL (y : ℝ) : HasDerivAt (fun y : ℝ => 1 + y • S) S y := by
    simpa using ((hasDerivAt_id y).smul_const S).const_add 1
  have hR (y : ℝ) : HasDerivAt (fun y : ℝ => 1 + y • T) T y := by
    simpa using ((hasDerivAt_id y).smul_const T).const_add 1
  have hd (y : ℝ) : HasDerivAt M (M' y) y := ((hL y).mul_const B).mul (hR y)
  have hdc : Continuous M' := by dsimp [M']; fun_prop
  have huL (y : ℝ) : IsUnit (1 + y • S) := (nilpotentShearUnit S hS y).isUnit
  have huR (y : ℝ) : IsUnit (1 + y • T) := (nilpotentShearUnit T hT y).isUnit
  have hu (y : ℝ) : IsUnit (M y) := ((huL y).mul hB).mul (huR y)
  have hz (y : ℝ) : τ (M' y * Ring.inverse (M y)) = 0 := by
    dsimp [M, M']
    rw [trace_derivative_mul_value τ hτ _ _ _ _ ((huL y).mul hB) (huR y),
      Ring.inverse_mul (Or.inl (huL y)), ← mul_assoc,
      Ring.mul_inverse_cancel_right B S hB,
      nilpotentShear_trace_derivative τ S hS htS,
      nilpotentShear_trace_derivative τ T hT htT, add_zero]
  have H (y : ℝ) : HasDerivAt (fun y => τ (CFC.log (star (M y) * M y))) 0 y := by
    simpa only [hz y, Complex.zero_re, mul_zero, Complex.ofReal_zero] using
      hasDerivAt_trace_log_star_mul_self τ hτ hstar hd hdc.continuousAt hu (x := y)
  have he := is_const_of_deriv_eq_zero (fun y => (H y).differentiableAt)
    (fun y => (H y).deriv) x 0
  simpa [M] using he

end TraceCFC

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ClosedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section SubTrace
variable {A : Type uA} [CStarAlgebra A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]

lemma subalgebra_log_coe (a : D) (ha : IsSelfAdjoint a) (hu : IsUnit a) :
    ((CFC.log a : D) : A) = CFC.log (a : A) := by
  exact D.subtype.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) Real.log a
    (Real.continuousOn_log.mono (fun x hx hzero =>
      (spectrum.zero_notMem_iff ℝ).mpr hu (by simpa only [Set.mem_singleton_iff.mp hzero] using hx)))
    continuous_subtype_val ha (ha.map D.subtype)

lemma subTrace_mul_comm (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a ∈ D, ∀ b ∈ D, τ (a * b) = τ (b * a)) (a b : D) :
    subTrace D τ (a * b) = subTrace D τ (b * a) := hτ a a.property b b.property

lemma subTrace_star (τ : A →L[ℝ] ℂ) (hτ : ∀ a, τ (star a) = star (τ a)) (a : D) :
    subTrace D τ (star a) = star (subTrace D τ a) := hτ a

lemma trace_log_shear_invariant_subalgebra (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a ∈ D, ∀ b ∈ D, τ (a * b) = τ (b * a))
    (hstar : ∀ a, τ (star a) = star (τ a))
    (B S T : D) (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : τ (S : A) = 0) (htT : τ (T : A) = 0) (x : ℝ) :
    τ (CFC.log (star ((1 + x • (S : A)) * (B : A) * (1 + x • (T : A))) *
      ((1 + x • (S : A)) * (B : A) * (1 + x • (T : A))))) =
      τ (CFC.log (star (B : A) * (B : A))) := by
  cases subsingleton_or_nontrivial D with
  | inl h =>
    have he : (1 + x • S) * B * (1 + x • T) = B := Subsingleton.elim _ _
    have he' := congrArg (fun a : D => (a : A)) he
    change (1 + x • (S : A)) * (B : A) * (1 + x • (T : A)) = (B : A) at he'
    rw [he']
  | inr h =>
    have H := trace_log_shear_invariant (subTrace D τ) (subTrace_mul_comm D τ hτ)
      (subTrace_star D τ hstar) B S T hB hS hT htS htT x
    have hM : IsUnit ((1 + x • S) * B * (1 + x • T)) :=
      (((nilpotentShearUnit S hS x).isUnit).mul hB).mul (nilpotentShearUnit T hT x).isUnit
    change τ ((CFC.log (star ((1 + x • S) * B * (1 + x • T)) *
      ((1 + x • S) * B * (1 + x • T))) : D) : A) =
      τ ((CFC.log (star B * B) : D) : A) at H
    rw [subalgebra_log_coe _ _ (IsSelfAdjoint.star_mul_self _) (hM.star.mul hM),
      subalgebra_log_coe _ _ (IsSelfAdjoint.star_mul_self _) (hB.star.mul hB)] at H
    exact H

end SubTrace

section ClosedTraceCalculus
variable {G : Type} [Group G] {n : ℕ}

theorem groupTrace_log_shear_invariant (B S T : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G))
    (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : ∑ i, (S i i).coeff 1 = 0) (htT : ∑ i, (T i i).coeff 1 = 0) (x : ℝ) :
    groupTrace (CFC.log (star ((1 + x • complexOperator S) * complexOperator B *
      (1 + x • complexOperator T)) * ((1 + x • complexOperator S) * complexOperator B *
      (1 + x • complexOperator T)))) =
      groupTrace (CFC.log (star (complexOperator B) * complexOperator B)) := by
  let B' := closedRepresentation B
  let S' := closedRepresentation S
  let T' := closedRepresentation T
  have hu : IsUnit B' := hB.map closedRepresentation
  have hs : S' * S' = 0 := by simpa [S'] using congrArg closedRepresentation hS
  have ht : T' * T' = 0 := by simpa [T'] using congrArg closedRepresentation hT
  have hcyc : ∀ a ∈ closedGroupAlgebra (G := G) (n := n),
      ∀ b ∈ closedGroupAlgebra (G := G) (n := n),
      groupTraceCLM (a * b) = groupTraceCLM (b * a) := by
    intro a ha b hb
    simp only [groupTraceCLM_apply]
    exact groupTrace_closed_mul_comm ha hb
  have hstar : ∀ a : Hilbert G n →L[ℂ] Hilbert G n,
      groupTraceCLM (star a) = star (groupTraceCLM a) := by
    simp only [groupTraceCLM_apply]
    exact groupTrace_star
  have hts : groupTraceCLM (S' : Hilbert G n →L[ℂ] Hilbert G n) = 0 := by
    simpa only [S', closedRepresentation_coe, groupTraceCLM_apply, groupTrace_complex] using htS
  have htt : groupTraceCLM (T' : Hilbert G n →L[ℂ] Hilbert G n) = 0 := by
    simpa only [T', closedRepresentation_coe, groupTraceCLM_apply, groupTrace_complex] using htT
  have H := trace_log_shear_invariant_subalgebra closedGroupAlgebra
    (groupTraceCLM.restrictScalars ℝ) hcyc hstar B' S' T' hu hs ht hts htt x
  change groupTraceCLM _ = groupTraceCLM _ at H
  simp only [groupTraceCLM_apply, S', B', T', closedRepresentation_coe] at H
  convert H using 1
  rfl

end ClosedTraceCalculus

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.WeightedProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section WeightedPair
variable {A : Type uA} [Ring A] [Algebra ℝ A]
lemma weightedPair_mul (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (a b c d e f : ℝ) :
    weightedPair Q R a b c * weightedPair Q R d e f = weightedPair Q R (a*d) (b*e) (c*f) := by
  simp only [weightedPair, add_mul, mul_add, smul_mul_smul_comm,
    mul_sub, sub_mul, one_mul, mul_one, hQ, hR, hQR, hRQ, smul_zero,
    smul_sub]
  module
lemma weightedPair_one (Q R : A) : weightedPair Q R 1 1 1 = 1 := by
  simp only [weightedPair, one_smul]; abel
lemma weightedPair_unit (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : IsUnit (weightedPair Q R a b c) := by
  refine ⟨⟨weightedPair Q R a b c, weightedPair Q R a⁻¹ b⁻¹ c⁻¹, ?_, ?_⟩, rfl⟩
  · rw [weightedPair_mul Q R hQ hR hQR hRQ, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb,
      mul_inv_cancel₀ hc, weightedPair_one]
  · rw [weightedPair_mul Q R hQ hR hQR hRQ, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb,
      inv_mul_cancel₀ hc, weightedPair_one]
lemma weightedPair_inverse (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Ring.inverse (weightedPair Q R a b c) = weightedPair Q R a⁻¹ b⁻¹ c⁻¹ := by
  have hu := weightedPair_unit Q R hQ hR hQR hRQ a b c ha hb hc
  apply_fun (weightedPair Q R a b c * ·) using IsUnit.mul_right_injective hu
  dsimp only
  rw [Ring.mul_inverse_cancel _ hu, weightedPair_mul Q R hQ hR hQR hRQ,
    mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_inv_cancel₀ hc, weightedPair_one]
end WeightedPair

section PairTrace
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

lemma trace_log_weightedPair (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (hQs : IsSelfAdjoint Q) (x : ℝ) :
    τ (CFC.log (star (weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1)) *
      weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1))) =
      (x * (2 * (τ (Q - R)).re) : ℝ) := by
  let M := fun y : ℝ => weightedPair Q R (Real.exp y) (-Real.exp (-y)) (-1)
  let M' := fun y : ℝ => weightedPair Q R (Real.exp y) (Real.exp (-y)) 0
  have hd (y : ℝ) : HasDerivAt M (M' y) y := by
    have h1 := (Real.hasDerivAt_exp y).smul_const Q
    have h2 := ((Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)).neg.smul_const R
    simpa [M, M', weightedPair] using (h1.add h2).add_const ((-1 : ℝ) • (1 - Q - R))
  have hdc : Continuous M' := by dsimp [M', weightedPair]; fun_prop
  have hu (y : ℝ) : IsUnit (M y) :=
    weightedPair_unit Q R hQ hR hQR hRQ _ _ _ (Real.exp_ne_zero y)
      (neg_ne_zero.mpr (Real.exp_ne_zero (-y))) (by norm_num)
  have hi (y : ℝ) : M' y * Ring.inverse (M y) = Q - R := by
    dsimp [M, M']
    rw [weightedPair_inverse Q R hQ hR hQR hRQ _ _ _ (Real.exp_ne_zero y)
      (neg_ne_zero.mpr (Real.exp_ne_zero (-y))) (by norm_num),
      weightedPair_mul Q R hQ hR hQR hRQ]
    simp [weightedPair, Real.exp_ne_zero, sub_eq_add_neg]
  have hdlog (y : ℝ) : HasDerivAt (fun y => τ (CFC.log (star (M y) * M y)))
      (2 * (τ (Q - R)).re : ℝ) y := by
    simpa only [hi y] using
      hasDerivAt_trace_log_star_mul_self τ hτ hstar hd hdc.continuousAt hu (x := y)
  have hdz (y : ℝ) : HasDerivAt (fun y => τ (CFC.log (star (M y) * M y)) -
      (y * (2 * (τ (Q - R)).re) : ℝ)) 0 y := by
    have hh := (((hasDerivAt_id y).mul_const (2 * (τ (Q - R)).re)).ofReal_comp)
    simpa only [Pi.sub_def, id_eq, one_mul, sub_self] using (hdlog y).sub hh
  have he := is_const_of_deriv_eq_zero (fun y => (hdz y).differentiableAt)
    (fun y => (hdz y).deriv) x 0
  have hz : star (M 0) * M 0 = 1 := by
    have he0 : M 0 = (2 : ℝ) • Q - 1 := by simp [M, weightedPair]; module
    rw [he0]
    simp only [star_sub, star_smul, star_one, hQs.star_eq, star_ofNat]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      mul_one, one_mul, hQ]
    module
  simp only [hz, CFC.log_one, map_zero, zero_mul, Complex.ofReal_zero, sub_zero] at he
  exact sub_eq_zero.mp he

end PairTrace

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.IndexedRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section OperatorStar
variable {G : Type} [Group G] {n : ℕ}

lemma complexOperator_star (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (star A) = star (complexOperator A) := by
  classical
  induction A using Matrix.induction_on' with
  | h_zero => simp [complexOperator_zero, star_zero (R := Hilbert G n →L[ℂ] Hilbert G n)]
  | h_add A B hA hB =>
    simp only [star_add, complexOperator_add, hA, hB,
      star_add (R := Hilbert G n →L[ℂ] Hilbert G n)]
  | h_std_basis i j a =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [complexOperator_zero, star_zero (R := Hilbert G n →L[ℂ] Hilbert G n)]
    | add a b ha hb =>
      simp only [Matrix.single_add, star_add, complexOperator_add, ha, hb,
        star_add (R := Hilbert G n →L[ℂ] Hilbert G n)]
    | single g z =>
      change complexOperator (Matrix.conjTranspose _) = _
      rw [Matrix.conjTranspose_single, star_groupAlgebra_single,
        complexOperator_single, complexOperator_single, star_smul, elementaryOperator_star]

end OperatorStar

section IndexedRepresentation
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]

lemma indexedComplexRepresentation_trace (A : Matrix I I (MonoidAlgebra ℂ G)) :
    groupTrace (indexedComplexRepresentation A) = ∑ i, (A i i).coeff 1 := by
  rw [show indexedComplexRepresentation A = complexOperator
    (Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A) from rfl,
    groupTrace_complex]
  exact (Fintype.equivFin I).symm.sum_comp (fun i => (A i i).coeff 1)

lemma indexedComplexRepresentation_star (A : Matrix I I (MonoidAlgebra ℂ G)) :
    indexedComplexRepresentation (star A) = star (indexedComplexRepresentation A) := by
  change complexOperator (Matrix.reindex _ _ (Matrix.conjTranspose A)) =
    star (complexOperator (Matrix.reindex _ _ A))
  rw [← Matrix.conjTranspose_reindex]
  exact complexOperator_star _

end IndexedRepresentation
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.WeightedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section ClosedPair
variable {A : Type uA} [CStarAlgebra A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]

lemma trace_log_weightedPair_subalgebra (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a ∈ D, ∀ b ∈ D, τ (a * b) = τ (b * a))
    (hstar : ∀ a, τ (star a) = star (τ a))
    (Q R : D) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (hQs : IsSelfAdjoint Q) (x : ℝ) :
    τ (CFC.log (star (weightedPair (Q : A) (R : A) (Real.exp x) (-Real.exp (-x)) (-1)) *
      weightedPair (Q : A) (R : A) (Real.exp x) (-Real.exp (-x)) (-1))) =
      (x * (2 * (τ ((Q : A) - (R : A))).re) : ℝ) := by
  cases subsingleton_or_nontrivial D with
  | inl h =>
    have hz : (0 : A) = 1 := congrArg (fun a : D => (a : A)) (Subsingleton.elim 0 1)
    let := subsingleton_of_zero_eq_one hz
    simp only [Subsingleton.elim (CFC.log _) (0 : A),
      Subsingleton.elim ((Q : A) - (R : A)) (0 : A), map_zero, Complex.zero_re,
      mul_zero, Complex.ofReal_zero]
  | inr h =>
    have H := trace_log_weightedPair (subTrace D τ) (subTrace_mul_comm D τ hτ)
      (subTrace_star D τ hstar) Q R hQ hR hQR hRQ hQs x
    let M := weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1)
    have hu : IsUnit M := weightedPair_unit Q R hQ hR hQR hRQ _ _ _
      (Real.exp_ne_zero x) (neg_ne_zero.mpr (Real.exp_ne_zero (-x))) (by norm_num)
    change τ ((CFC.log (star M * M) : D) : A) = _ at H
    rw [subalgebra_log_coe _ _ (IsSelfAdjoint.star_mul_self _) (hu.star.mul hu)] at H
    exact H

end ClosedPair

section IndexedTraceCalculus
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]

lemma indexedClosedRepresentation_star (A : Matrix I I (MonoidAlgebra ℂ G)) :
    indexedClosedRepresentation (star A) = star (indexedClosedRepresentation A) :=
  Subtype.ext (indexedComplexRepresentation_star A)

lemma indexed_trace_log_weightedPair (Q R : Matrix I I (MonoidAlgebra ℂ G))
    (hQ : Q * Q = Q) (hR : R * R = R) (hQR : Q * R = 0) (hRQ : R * Q = 0)
    (hQs : IsSelfAdjoint Q) (x : ℝ) :
    let M := indexedComplexRepresentation (weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1))
    groupTrace (CFC.log (star M * M)) =
      (x * (2 * (∑ i, ((Q - R) i i).coeff 1).re) : ℝ) := by
  let φ := indexedClosedRepresentation (G := G) (I := I)
  have hQ' : φ Q * φ Q = φ Q := by rw [← map_mul, hQ]
  have hR' : φ R * φ R = φ R := by rw [← map_mul, hR]
  have hQR' : φ Q * φ R = 0 := by rw [← map_mul, hQR, map_zero]
  have hRQ' : φ R * φ Q = 0 := by rw [← map_mul, hRQ, map_zero]
  have hQs' : IsSelfAdjoint (φ Q) := by
    change star (φ Q) = φ Q
    rw [← indexedClosedRepresentation_star, hQs.star_eq]
  have hcyc : ∀ a ∈ closedGroupAlgebra (G := G) (n := Fintype.card I),
      ∀ b ∈ closedGroupAlgebra, groupTraceCLM (a * b) = groupTraceCLM (b * a) := by
    intro a ha b hb
    simp only [groupTraceCLM_apply]
    exact groupTrace_closed_mul_comm ha hb
  have hstar : ∀ a : Hilbert G (Fintype.card I) →L[ℂ] Hilbert G (Fintype.card I),
      groupTraceCLM (star a) = star (groupTraceCLM a) := by
    simp only [groupTraceCLM_apply]
    exact groupTrace_star
  have H := trace_log_weightedPair_subalgebra closedGroupAlgebra
    (groupTraceCLM.restrictScalars ℝ) hcyc hstar (φ Q) (φ R) hQ' hR' hQR' hRQ' hQs' x
  change groupTraceCLM (G := G) (n := Fintype.card I) _ =
    ((x * (2 * (groupTraceCLM (G := G) (n := Fintype.card I) _).re) : ℝ) : ℂ) at H
  simp only [groupTraceCLM_apply, φ, indexedClosedRepresentation_coe] at H
  have hmap (a b c : ℝ) : indexedComplexRepresentation (weightedPair Q R a b c) =
      weightedPair (indexedComplexRepresentation Q) (indexedComplexRepresentation R) a b c := by
    simp only [weightedPair, map_add, map_sub, map_one, AlgHom.map_smul_of_tower]
  have ht : groupTrace (indexedComplexRepresentation Q - indexedComplexRepresentation R) =
      ∑ i, ((Q - R) i i).coeff 1 := by
    rw [← map_sub, indexedComplexRepresentation_trace]
  dsimp only
  rw [hmap]
  rw [ht] at H
  convert H using 1
  rfl

end IndexedTraceCalculus
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ShearTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section IndexedShear
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]
lemma indexed_trace_log_shear (B S T : Matrix I I (MonoidAlgebra ℂ G))
    (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : ∑ i, (S i i).coeff 1 = 0) (htT : ∑ i, (T i i).coeff 1 = 0) :
    let φ := indexedComplexRepresentation (G := G) (I := I)
    groupTrace (CFC.log (star (φ ((1 + S) * B * (1 + T))) * φ ((1 + S) * B * (1 + T)))) =
      groupTrace (CFC.log (star (φ B) * φ B)) := by
  let e := Matrix.reindexAlgEquiv ℂ (MonoidAlgebra ℂ G) (Fintype.equivFin I)
  have hs : e S * e S = 0 := by rw [← map_mul, hS, map_zero]
  have ht : e T * e T = 0 := by rw [← map_mul, hT, map_zero]
  have hts : ∑ i, ((e S) i i).coeff 1 = 0 :=
    ((Fintype.equivFin I).symm.sum_comp (fun i => (S i i).coeff 1)).trans htS
  have htt : ∑ i, ((e T) i i).coeff 1 = 0 :=
    ((Fintype.equivFin I).symm.sum_comp (fun i => (T i i).coeff 1)).trans htT
  have H := groupTrace_log_shear_invariant (e B) (e S) (e T)
    (hB.map e.toRingHom) hs ht hts htt 1
  change groupTrace (CFC.log (star (complexOperator (e ((1 + S) * B * (1 + T)))) *
    complexOperator (e ((1 + S) * B * (1 + T))))) =
      groupTrace (CFC.log (star (complexOperator (e B)) * complexOperator (e B)))
  simpa only [map_mul, map_add, map_one, complexOperator_mul, complexOperator_add,
    complexOperator_one, one_smul] using H
end IndexedShear
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.TransferTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section TransferTrace
variable {G r m : Type} [Group G] [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

lemma lowerNil_square (U : Matrix m r (MonoidAlgebra ℂ G)) : lowerNil U * lowerNil U = 0 := by
  simp [lowerNil, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
lemma upperNil_square (V : Matrix r m (MonoidAlgebra ℂ G)) : upperNil V * upperNil V = 0 := by
  simp [upperNil, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
omit [Fintype r] [Fintype m] in
lemma lowerShear_eq_one_add (U : Matrix m r (MonoidAlgebra ℂ G)) :
    lowerShear U = 1 + lowerNil U := by
  rw [lowerShear, lowerNil, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
  simp
omit [Fintype r] [Fintype m] in
lemma upperShear_eq_one_add (V : Matrix r m (MonoidAlgebra ℂ G)) :
    upperShear V = 1 + upperNil V := by
  rw [upperShear, upperNil, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
  simp

lemma transfer_diagonal_weightedPair (q : ℝ) (P : Matrix m m (MonoidAlgebra ℂ G)) :
    Matrix.fromBlocks (q • (1 : Matrix r r (MonoidAlgebra ℂ G))) 0 0
      (projectionReweight P (-q⁻¹) (-1 : ℝ)) =
      weightedPair topBlockIdentity (bottomBlock P) q (-q⁻¹) (-1) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j <;>
      simp [weightedPair, topBlockIdentity, bottomBlock, Matrix.fromBlocks, hij]
  · simp [weightedPair, topBlockIdentity, bottomBlock, Matrix.fromBlocks]
  · simp [weightedPair, topBlockIdentity, bottomBlock, Matrix.fromBlocks]
  · simp [weightedPair, topBlockIdentity, bottomBlock, projectionReweight,
      Matrix.fromBlocks, Matrix.one_apply]

lemma transfer_trace_log (q : ℝ) (hq : 0 < q)
    (P : Matrix m m (MonoidAlgebra ℂ G)) (hP : P * P = P)
    (U : Matrix m r (MonoidAlgebra ℂ G)) (V : Matrix r m (MonoidAlgebra ℂ G)) :
    let M := indexedComplexRepresentation (transferMatrix q P U V)
    groupTrace (CFC.log (star M * M)) =
      (2 * ((Fintype.card r : ℝ) - (∑ i, (P i i).coeff 1).re) * Real.log q : ℝ) := by
  let Q : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := topBlockIdentity
  let R : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := bottomBlock P
  have hQ : Q * Q = Q := by simp [Q, topBlockIdentity, Matrix.fromBlocks_multiply]
  have hR : R * R = R := by simp [R, bottomBlock, Matrix.fromBlocks_multiply, hP]
  have hQR : Q * R = 0 := by
    simp [Q, R, topBlockIdentity, bottomBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
  have hRQ : R * Q = 0 := by
    simp [Q, R, topBlockIdentity, bottomBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
  have hQs : IsSelfAdjoint Q := by
    change Matrix.conjTranspose Q = Q
    simp [Q, topBlockIdentity, Matrix.fromBlocks_conjTranspose]
  let B := weightedPair Q R q (-q⁻¹) (-1)
  have hB : IsUnit B := weightedPair_unit Q R hQ hR hQR hRQ _ _ _
    hq.ne' (neg_ne_zero.mpr (inv_ne_zero hq.ne')) (by norm_num)
  let S := lowerNil (q⁻¹ • U)
  let T := upperNil (q⁻¹ • V)
  have htS : ∑ i, (S i i).coeff 1 = 0 := by simp [S, lowerNil, Fintype.sum_sum_type]
  have htT : ∑ i, (T i i).coeff 1 = 0 := by simp [T, upperNil, Fintype.sum_sum_type]
  have hf : transferMatrix q P U V = (1 + S) * B * (1 + T) := by
    rw [← transferMatrix_factorization q hq.ne', transfer_diagonal_weightedPair,
      lowerShear_eq_one_add, upperShear_eq_one_add]
  have H := indexed_trace_log_shear B S T hB (lowerNil_square _) (upperNil_square _) htS htT
  have H' := indexed_trace_log_weightedPair Q R hQ hR hQR hRQ hQs (Real.log q)
  have hexp : Real.exp (Real.log q) = q := Real.exp_log hq
  have hexpn : Real.exp (-Real.log q) = q⁻¹ := by rw [Real.exp_neg, hexp]
  dsimp only at H H' ⊢
  rw [hf, H]
  have ht : (∑ i, ((Q - R) i i).coeff 1) =
      (Fintype.card r : ℂ) - ∑ i, (P i i).coeff 1 := by
    simp [Q, R, topBlockIdentity, bottomBlock, Fintype.sum_sum_type]
  rw [hexp, hexpn, ht] at H'
  calc
    _ = ((Real.log q * (2 * ((Fintype.card r : ℂ) - ∑ i, (P i i).coeff 1).re) : ℝ) : ℂ) := H'
    _ = _ := by congr 1; simp only [Complex.sub_re, Complex.natCast_re]; ring

end TransferTrace
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.RationalRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section RationalMap
variable {G I J : Type} [Group G]

lemma rationalComplexMap_smul (q : ℚ) (A : Matrix I J (MonoidAlgebra ℚ G)) :
    (q • A).map rationalComplexMap = (q : ℝ) • A.map rationalComplexMap := by
  apply Matrix.ext
  intro i j
  change rationalComplexMap (q • A i j) = (q : ℝ) • rationalComplexMap (A i j)
  rw [map_rat_smul, Rat.cast_smul_eq_qsmul ℝ]

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
omit [Fintype J] in
lemma transferMatrix_map_complex (q : ℚ) (P : Matrix J J (MonoidAlgebra ℚ G))
    (U : Matrix J I (MonoidAlgebra ℚ G)) (V : Matrix I J (MonoidAlgebra ℚ G)) :
    (transferMatrix q P U V).map rationalComplexMap =
      transferMatrix (q : ℝ) (P.map rationalComplexMap) (U.map rationalComplexMap)
        (V.map rationalComplexMap) := by
  simp only [transferMatrix, Matrix.fromBlocks_map, rationalComplexMap_smul,
    Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_sub _ (map_sub _) _ _, Matrix.map_mul, Rat.cast_inv]

omit [DecidableEq I] in
lemma rationalComplexMap_trace (P : Matrix I I (MonoidAlgebra ℚ G)) :
    (∑ i, ((P.map rationalComplexMap) i i).coeff 1).re =
      ((∑ i, (P i i).coeff 1 : ℚ) : ℝ) := by
  simp [Matrix.map_apply, rationalComplexMap]

lemma reindexed_rational_isUnit (A : Matrix I I (MonoidAlgebra ℤ G))
    (hA : IsUnit (A.map toRat)) :
    IsUnit (rationalMatrix (Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A)) :=
  hA.map (Matrix.reindexRingEquiv (MonoidAlgebra ℚ G) (Fintype.equivFin I)).toRingHom

lemma rationalIndexed_integer (A : Matrix I I (MonoidAlgebra ℤ G)) :
    indexedComplexRepresentation ((A.map toRat).map rationalComplexMap) =
      regularOperator (Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A) := by
  have hf : rationalComplexMap.comp (toRat (G := G)) =
      MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) := by
    rw [rationalComplexMap, toRat, ← MonoidAlgebra.mapRingHom_comp]
    congr 1
  change complexOperator ((Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A).map
    (rationalComplexMap.comp (toRat (G := G)))) = _
  rw [hf, complexOperator_integer]

end RationalMap
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ProjectionCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section ProjectionCriterion
variable {G r m : Type} [Group G] [Group.FG G]
variable [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m] [Nonempty r]

theorem projection_criterion_oai (D : ℕ) (hodd : Odd D)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P ∧ IsSelfAdjoint P)
    (htrace : (Fintype.card r : ℚ) < ∑ i, (P i i).coeff 1)
    (Z : Matrix m m (MonoidAlgebra ℤ G)) (hZ : Z.map toRat = (D : ℚ) • P)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G)) (huv : u * v = Z.map (toMod 2)) :
    MainStatement := by
  obtain ⟨k, hk, hq, hqD⟩ := exists_binary_modulus D hodd.pos hodd
  obtain ⟨U, V, A, hA, hAu⟩ := integral_transfer_of_congruence D hodd P hP.1 Z hZ u v huv k hk hqD
  let e := Fintype.equivFin (r ⊕ m)
  let A' := Matrix.reindex e e A
  have hAu' : IsUnit (rationalMatrix A') := reindexed_rational_isUnit A hAu
  have hqR : (1 : ℝ) < (2 ^ k : ℕ) := by exact_mod_cast hq
  have hPC : P.map rationalComplexMap * P.map rationalComplexMap = P.map rationalComplexMap := by
    rw [← Matrix.map_mul, hP.1]
  have hOp : regularOperator A' = indexedComplexRepresentation
      (transferMatrix (((2 ^ k : ℕ) : ℚ) : ℝ) (P.map rationalComplexMap)
        ((U.map toRat).map rationalComplexMap) ((V.map toRat).map rationalComplexMap)) := by
    rw [← rationalIndexed_integer A, hA, transferMatrix_map_complex]
  have hlog := transfer_trace_log (((2 ^ k : ℕ) : ℚ) : ℝ)
    (lt_trans zero_lt_one hqR) (P.map rationalComplexMap) hPC
      ((U.map toRat).map rationalComplexMap) ((V.map toRat).map rationalComplexMap)
  dsimp only at hlog
  rw [← hOp, rationalComplexMap_trace] at hlog
  have htraceR : (Fintype.card r : ℝ) < ((∑ i, (P i i).coeff 1 : ℚ) : ℝ) := by
    exact_mod_cast htrace
  have hn : 2 * ((Fintype.card r : ℝ) - ((∑ i, (P i i).coeff 1 : ℚ) : ℝ)) *
      Real.log (((2 ^ k : ℕ) : ℚ) : ℝ) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr htraceR))
      (Real.log_pos (by simpa using hqR))
  refine ⟨G, inferInstance, inferInstance, Fintype.card (r ⊕ m),
    Fintype.card_pos, A', regularOperator A', hAu', regularOperator_spec A',
    regularOperator_isUnit hAu', fkDet_pos _, ?_⟩
  unfold fkDet
  apply Real.exp_lt_one_iff.mpr
  rw [hlog, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos hn (by norm_num)

end ProjectionCriterion
end GroupRingDeterminant

end

end OAI
end

theorem solution : type_of% @OAI.GroupRingDeterminant.projection_criterion_oai := @OAI.GroupRingDeterminant.projection_criterion_oai
