-- Prove2me | solution 1 for LatticePrepro.exists_explicit_momentRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:34:52.105228+00:00
-- url     : https://prove2.me/submissions/1eb84a78-267f-4226-b390-4d2a02c0ba7d

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Theorems.Thm_LatticePrepro_ExplicitTables_natDegree_elemProd_le
import Theorems.Thm_LatticePrepro_ExplicitTables_soundness_setup
import Theorems.Thm_LatticePrepro_FieldSetup_exists_fieldSetup
import Theorems.Thm_LatticePrepro_digitVal_gdigits
import Theorems.Thm_LatticePrepro_exists_pow_between
import Theorems.Thm_LatticePrepro_gdigits_le
import Theorems.Thm_LatticePrepro_hankel_reconstruction

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ExplicitTables end LatticePrepro.ExplicitTables

namespace LatticePrepro

/-- The geometric identity `(B - 1) · ∑_{h<m} B^h + 1 = B^m`, without subtraction. -/
lemma pred_mul_geomSum_add_one {B : ℕ} (hB : 1 ≤ B) (m : ℕ) :
    (B - 1) * (∑ h ∈ Finset.range m, B ^ h) + 1 = B ^ m := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, pow_succ]
    ring

/-- The geometric identity `(B - 1) · ∑_{h<m} B^h = B^m - 1`. -/
lemma pred_mul_geomSum {B : ℕ} (hB : 1 ≤ B) (m : ℕ) :
    (B - 1) * (∑ h ∈ Finset.range m, B ^ h) = B ^ m - 1 := by
  have := pred_mul_geomSum_add_one hB m
  omega

end LatticePrepro

namespace LatticePrepro

/-- An exponent vector with entries at most `c · (B - 1)` has value at most `c · (B^m - 1)`. -/
theorem digitVal_le_of_le {B m c : ℕ} (hB : 2 ≤ B) (η : Fin m → ℕ)
    (hη : ∀ h, η h ≤ c * (B - 1)) : digitVal B η ≤ c * (B ^ m - 1) := by
  unfold digitVal
  calc ∑ h : Fin m, η h * B ^ (h : ℕ) ≤ ∑ h : Fin m, c * (B - 1) * B ^ (h : ℕ) :=
        Finset.sum_le_sum fun h _ => Nat.mul_le_mul_right _ (hη h)
    _ = c * ((B - 1) * ∑ h ∈ Finset.range m, B ^ h) := by
        rw [Fin.sum_univ_eq_sum_range (fun h => c * (B - 1) * B ^ h) m, Finset.mul_sum,
          Finset.mul_sum]
        simp only [mul_assoc]
    _ = c * (B ^ m - 1) := by rw [pred_mul_geomSum (by omega)]

end LatticePrepro

namespace LatticePrepro

namespace FieldSetup

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ}

variable (FS : FieldSetup p d δ)

/-- The powers of `γ` are `𝔽_p`-linearly independent as well. -/
lemma linearIndependent_pow_zmod :
    LinearIndependent (ZMod p) (fun i : Fin δ => FS.γ ^ (i : ℕ)) :=
  FS.linearIndependent_pow.restrict_scalars (by
    intro a b hab
    simpa using (algebraMap (ZMod p) FS.𝕊).injective (by simpa [Algebra.smul_def] using hab))

end FieldSetup

end LatticePrepro

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

section Linearity

variable {FS m}

lemma colSum_zero (η : Fin m → ℕ) (s : FS.𝕊) : colSum FS m (0 : Coord FS m → ZMod p) η s = 0 := by
  simp [colSum]

lemma colSum_add (y y' : Coord FS m → ZMod p) (η : Fin m → ℕ) (s : FS.𝕊) :
    colSum FS m (y + y') η s = colSum FS m y η s + colSum FS m y' η s := by
  simp [colSum, add_smul, Finset.sum_add_distrib]

lemma interp_zero (η : Fin m → ℕ) : interp FS m (0 : Coord FS m → ZMod p) η = 0 := by
  unfold interp
  have : (fun s => colSum FS m (0 : Coord FS m → ZMod p) η s) = 0 := by
    funext s; exact colSum_zero η s
  rw [this, map_zero]

lemma interp_add (y y' : Coord FS m → ZMod p) (η : Fin m → ℕ) :
    interp FS m (y + y') η = interp FS m y η + interp FS m y' η := by
  unfold interp
  have : (fun s => colSum FS m (y + y') η s) =
      (fun s => colSum FS m y η s) + (fun s => colSum FS m y' η s) := by
    funext s; exact colSum_add y y' η s
  rw [this, map_add]

variable {B}

lemma mom_zero (k : ℕ) : mom FS m B (0 : Coord FS m → ZMod p) k = 0 := by
  simp [mom, interp_zero]

lemma mom_add (y y' : Coord FS m → ZMod p) (k : ℕ) :
    mom FS m B (y + y') k = mom FS m B y k + mom FS m B y' k := by
  simp [mom, interp_add]

end Linearity

section Interpolation

variable {FS m}

/-- Interpolation uniqueness: a polynomial of degree `< q` with the right values is the
interpolant. -/
lemma interp_eq_of_eval_eq (y : Coord FS m → ZMod p) (η : Fin m → ℕ) {f : FS.𝕊[X]}
    (hf : f.degree < Fintype.card FS.𝕊) (h : ∀ s, eval s f = colSum FS m y η s) :
    interp FS m y η = f := by
  unfold interp
  exact (Lagrange.eq_interpolate_of_eval_eq (s := (Finset.univ : Finset FS.𝕊)) (v := id)
    (r := fun s => colSum FS m y η s) (Set.injOn_id _) (by simpa using hf)
    (fun s _ => by simpa using h s)).symm

end Interpolation

lemma IdxSet.toNat_le {p m B : ℕ} (η : IdxSet p m B) (h : Fin m) :
    η.toNat h ≤ 2 * p * (B - 1) := Nat.lt_succ_iff.mp (η h).isLt

/-- `K` has characteristic `p`. -/
lemma charP_K : CharP FS.K p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) FS.K).injective p

lemma constraintFun_zero : constraintFun FS m B (0 : Coord FS m → ZMod p) = 0 := by
  have := charP_K FS
  simp only [constraintFun, interp_zero, coeff_zero, ite_self, map_zero, mom_zero, sub_self,
    zero_pow (Fact.out : p.Prime).ne_zero]
  rfl

lemma constraintFun_add (y y' : Coord FS m → ZMod p) :
    constraintFun FS m B (y + y') = constraintFun FS m B y + constraintFun FS m B y' := by
  have := charP_K FS
  simp only [constraintFun, interp_add, coeff_add, map_add, mom_add, Prod.mk_add_mk,
    Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext ηu
    simp only [Pi.add_apply]
    split_ifs <;> simp
  · funext η
    simp only [Pi.add_apply]
    ring
  · funext k
    simp only [Pi.add_apply]
    split_ifs with h
    · rw [add_pow_char]
      ring
    · simp

/-- The constraint map as an `𝔽_p`-linear map. -/
noncomputable def constraintₗ : (Coord FS m → ZMod p) →ₗ[ZMod p] ConstrW FS m B :=
  AddMonoidHom.toZModLinearMap p
    { toFun := constraintFun FS m B
      map_zero' := constraintFun_zero FS m B
      map_add' := constraintFun_add FS m B }

@[simp] lemma constraintₗ_apply (y : Coord FS m → ZMod p) :
    constraintₗ FS m B y = constraintFun FS m B y := rfl

/-- The moment maps as `𝔽_p`-linear maps. -/
noncomputable def momₗ (k : ℕ) : (Coord FS m → ZMod p) →ₗ[ZMod p] FS.K :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun y => mom FS m B y k
      map_zero' := mom_zero k
      map_add' := fun y y' => mom_add y y' k }

@[simp] lemma momₗ_apply (k : ℕ) (y : Coord FS m → ZMod p) : momₗ FS m B k y = mom FS m B y k :=
  rfl

section Unpack

variable {FS m B}

/-- Frobenius constraint. -/
lemma mom_mul_eq_pow_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) {k : ℕ} (hk : p * k ≤ maxOrder p m B) :
    mom FS m B y (p * k) = (mom FS m B y k) ^ p := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hk' : k < maxOrder p m B + 1 := by
    have : k ≤ p * k := Nat.le_mul_of_pos_left k hp
    omega
  have := congrFun (congrArg (fun w => w.2.2) hy) ⟨k, hk'⟩
  simpa [constraintFun, hk, sub_eq_zero] using this

end Unpack

end ExplicitTables

end LatticePrepro

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

lemma aeval_elemPoly (α : FS.K) (h : Fin m) :
    aeval FS.γ (elemPoly FS m B α h) = α ^ B ^ (h : ℕ) :=
  (FS.exists_aeval (α ^ B ^ (h : ℕ))).choose_spec.2

/-- The label of `α` in column `s`. -/
noncomputable def elemLabel (α : FS.K) (s : FS.𝕊) : Fin m → FS.𝕊 :=
  fun h => eval s (elemPoly FS m B α h)

/-- The element table `ê_α`. -/
noncomputable def elemTab (α : FS.K) : Coord FS m → ZMod p :=
  fun ls => if ls.1 = elemLabel FS m B α ls.2 then 1 else 0

variable {FS m B}

lemma elemTab_binary (α : FS.K) : IsBinary (elemTab FS m B α) := by
  intro ls
  unfold elemTab
  split_ifs <;> simp

lemma blockSupport_elemTab (α : FS.K) (s : FS.𝕊) :
    blockSupport Prod.snd (elemTab FS m B α) s = {(elemLabel FS m B α s, s)} := by
  ext ⟨lam, s'⟩
  rw [blockSupport, Finset.mem_filter, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨?_, rfl⟩
    by_contra hne
    exact h (by simp [elemTab, hne])
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, by simp [elemTab]⟩

lemma elemTab_onePerBlock (α : FS.K) : ExactlyOnePerBlock Prod.snd (elemTab FS m B α) := by
  intro s
  rw [blockSupport_elemTab, Finset.card_singleton]

/-- The column sums of the element table. -/
lemma colSum_elemTab (α : FS.K) (η : Fin m → ℕ) (s : FS.𝕊) :
    colSum FS m (elemTab FS m B α) η s = ∏ h, elemLabel FS m B α s h ^ η h := by
  unfold colSum elemTab
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (elemLabel FS m B α s)]
  simp

lemma eval_elemProd (α : FS.K) (η : Fin m → ℕ) (s : FS.𝕊) :
    eval s (elemProd FS m B α η) = ∏ h, elemLabel FS m B α s h ^ η h := by
  unfold elemProd elemLabel
  simp [eval_prod, eval_pow]

lemma aeval_elemProd (α : FS.K) (η : Fin m → ℕ) :
    aeval FS.γ (elemProd FS m B α η) = α ^ digitVal B η := by
  unfold elemProd digitVal
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [map_pow, aeval_elemPoly, ← pow_mul, mul_comm]

/-- The interpolants of the element table are the product polynomials. -/
lemma interp_elemTab (hΔ : degBound p m B δ < Fintype.card FS.𝕊) (α : FS.K) {η : Fin m → ℕ}
    (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    interp FS m (elemTab FS m B α) η = elemProd FS m B α η := by
  apply interp_eq_of_eval_eq
  · calc (elemProd FS m B α η).degree ≤ (elemProd FS m B α η).natDegree := degree_le_natDegree
      _ < Fintype.card FS.𝕊 := by
        exact_mod_cast lt_of_le_of_lt (natDegree_elemProd_le α hη) hΔ
  · intro s
    rw [eval_elemProd, colSum_elemTab]

lemma aeval_interp_elemTab (hΔ : degBound p m B δ < Fintype.card FS.𝕊) (α : FS.K)
    {η : Fin m → ℕ} (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    aeval FS.γ (interp FS m (elemTab FS m B α) η) = α ^ digitVal B η := by
  rw [interp_elemTab hΔ α hη, aeval_elemProd]

/-- Generalized digits of admissible orders are admissible exponents. -/
lemma gdigits_le_of_le (hB : 2 ≤ B) (hm : 1 ≤ m) {k : ℕ} (hk : k ≤ 2 * p * (B ^ m - 1))
    (h : Fin m) : gdigits B m k h ≤ 2 * p * (B - 1) := by
  have hp : 1 ≤ 2 * p := by have := (Fact.out : p.Prime).pos; omega
  exact gdigits_le hB hm hp hk h

/-- The moments of the element table are the powers of `α`. -/
lemma mom_elemTab (hB : 2 ≤ B) (hm : 1 ≤ m) (hΔ : degBound p m B δ < Fintype.card FS.𝕊)
    (α : FS.K) {k : ℕ} (hk : k ≤ 2 * p * (B ^ m - 1)) :
    mom FS m B (elemTab FS m B α) k = α ^ k := by
  unfold mom
  rw [aeval_interp_elemTab hΔ α (gdigits_le_of_le hB hm hk), digitVal_gdigits hB hm]

/-- The element table satisfies the evaluation table constraints. -/
lemma constraintFun_elemTab (hB : 2 ≤ B) (hm : 1 ≤ m) (hΔ : degBound p m B δ < Fintype.card FS.𝕊)
    (α : FS.K) : constraintFun FS m B (elemTab FS m B α) = 0 := by
  have hval : ∀ η : IdxSet p m B, digitVal B η.toNat ≤ 2 * p * (B ^ m - 1) :=
    fun η => digitVal_le_of_le hB η.toNat η.toNat_le
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext ηu
    simp only [constraintFun, Pi.zero_apply, Prod.fst_zero]
    split_ifs with hu
    · rw [interp_elemTab hΔ α ηu.1.toNat_le]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_elemProd_le α ηu.1.toNat_le) hu)
    · rfl
  · funext η
    simp only [constraintFun, Pi.zero_apply, Prod.snd_zero, Prod.fst_zero]
    rw [aeval_interp_elemTab hΔ α η.toNat_le, mom_elemTab hB hm hΔ α (hval η), sub_self]
  · funext k
    simp only [constraintFun, Pi.zero_apply, Prod.snd_zero]
    split_ifs with hk
    · unfold maxOrder at hk
      have hp : 1 ≤ p := (Fact.out : p.Prime).pos
      have hk' : k.val ≤ 2 * p * (B ^ m - 1) :=
        le_trans (Nat.le_mul_of_pos_left k.val hp) hk
      rw [mom_elemTab hB hm hΔ α hk, mom_elemTab hB hm hΔ α hk', ← pow_mul, mul_comm, sub_self]
    · rfl

/-- **Completeness** of the explicit moment representation. -/
theorem elemTab_complete (hB : 2 ≤ B) (hm : 1 ≤ m) (hΔ : degBound p m B δ < Fintype.card FS.𝕊)
    (α : FS.K) :
    IsBinary (elemTab FS m B α) ∧ ExactlyOnePerBlock Prod.snd (elemTab FS m B α) ∧
      constraintFun FS m B (elemTab FS m B α) = 0 ∧
      ∀ k ≤ 2 * B ^ m - 2, mom FS m B (elemTab FS m B α) k = α ^ k := by
  refine ⟨elemTab_binary α, elemTab_onePerBlock α, constraintFun_elemTab hB hm hΔ α, ?_⟩
  intro k hk
  apply mom_elemTab hB hm hΔ α
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have h1 : 1 ≤ B ^ m := Nat.one_le_pow _ _ (by omega)
  calc k ≤ 2 * B ^ m - 2 := hk
    _ = 2 * (B ^ m - 1) := by omega
    _ ≤ 2 * p * (B ^ m - 1) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left _ hp)

end ExplicitTables

end LatticePrepro

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

/-- The encoding tuple `(0, 1, γ, …, γ^{S-1})` of a field setup of degree `δ ≥ S`. -/
noncomputable def encodingTuple {S δ : ℕ} (FS : FieldSetup p d δ) (hS : S ≤ δ) :
    EncodingTuple p FS.K S where
  E := fun i => if i = 0 then 0 else FS.γ ^ (i.val - 1)
  E_zero := by simp
  linearIndependent := by
    have := FS.linearIndependent_pow_zmod.comp (Fin.castLE hS) (Fin.castLE_injective hS)
    convert this using 1
    funext i
    simp [Fin.succ_ne_zero]

variable {δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

lemma card_fiber_snd (s : FS.𝕊) :
    (Finset.univ.filter fun i : Coord FS m => i.2 = s).card = Fintype.card (Fin m → FS.𝕊) := by
  rw [← Finset.card_univ]
  refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro i hi i' hi' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact Prod.ext h (hi.trans hi'.symm)
  · intro lam _
    exact ⟨(lam, s), by simp, rfl⟩

variable {FS m B}

omit [Fact p.Prime] in
lemma maxOrder_eq (m B : ℕ) : 2 * hankelLen p (B ^ m) - 2 = maxOrder p m B := by
  unfold hankelLen maxOrder
  rw [mul_assoc]
  omega

lemma two_mul_sub_two_lt_hankelLen (hB : 2 ≤ B) {k : ℕ} (hk : k ≤ 2 * B ^ m - 2) :
    k < hankelLen p (B ^ m) := by
  unfold hankelLen
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : 1 ≤ B ^ m := Nat.one_le_pow _ _ (by omega)
  have : 2 * (B ^ m - 1) ≤ p * (B ^ m - 1) := Nat.mul_le_mul_right _ hp
  omega

/-- **Soundness** of the explicit moment representation. -/
theorem rep_sound (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) (y : Coord FS m → ZMod p)
    (hy : constraintFun FS m B y = 0) (hw : 2 * hammingNorm y < B ^ m * Fintype.card FS.𝕊) :
    ∃ f : AlgebraicClosure FS.K →₀ ZMod p,
      (∀ k ≤ 2 * B ^ m - 2,
        algebraMap FS.K (AlgebraicClosure FS.K) (mom FS m B y k) = moment f k) ∧
      Fintype.card FS.𝕊 * f.support.card ≤ 2 * hammingNorm y := by
  obtain ⟨t, htr, hqt, c, hc, hdep⟩ := soundness_setup hB hm hΔ hy hw
  set Ω := AlgebraicClosure FS.K
  let y' : ℕ → Ω := fun k => algebraMap FS.K Ω (mom FS m B y k)
  have hr : 2 ≤ B ^ m := le_trans hB (Nat.le_self_pow (by omega) B)
  have hfrob : ∀ k, p * k ≤ 2 * hankelLen p (B ^ m) - 2 → y' (p * k) = y' k ^ p := by
    intro k hk
    rw [maxOrder_eq] at hk
    simp only [y']
    rw [mom_mul_eq_pow_of_constraint hy hk, map_pow]
  have hdep' : ∃ c' : Fin (t + 1) → Ω, c' ≠ 0 ∧
      ∀ i : Fin (hankelLen p (B ^ m)), ∑ j, c' j * y' (i.val + j.val) = 0 := by
    refine ⟨fun j => algebraMap FS.K Ω (c j), ?_, ?_⟩
    · intro h0
      apply hc
      funext j
      have := congrFun h0 j
      simpa using (algebraMap FS.K Ω).injective (by simpa using this)
    · intro i
      simp only [y']
      rw [show (∑ x, algebraMap FS.K Ω (c x) * algebraMap FS.K Ω (mom FS m B y (i.val + x.val))) =
          algebraMap FS.K Ω (∑ x, c x * mom FS m B y (i.val + x.val)) by simp [map_sum, map_mul]]
      rw [hdep i, map_zero]
  obtain ⟨f, hf, hmom⟩ := hankel_reconstruction hr y' hfrob htr hdep'
  refine ⟨f, fun k hk => ?_, ?_⟩
  · exact hmom k (two_mul_sub_two_lt_hankelLen hB hk)
  · calc Fintype.card FS.𝕊 * f.support.card ≤ Fintype.card FS.𝕊 * t := Nat.mul_le_mul_left _ hf
      _ ≤ 2 * hammingNorm y := hqt

variable (FS m B)

/-- The explicit moment representation (Theorem A.8, representation part). -/
noncomputable def rep (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) :
    MomentRepresentation p FS.K (AlgebraicClosure FS.K) where
  r := B ^ m
  two_le_r := le_trans hB (Nat.le_self_pow (by omega) B)
  ι := Coord FS m
  β := FS.𝕊
  blk := Prod.snd
  blockSize := Fintype.card (Fin m → FS.𝕊)
  card_fiber := card_fiber_snd FS m
  W := ConstrW FS m B
  constraint := constraintₗ FS m B
  momentMap := fun k => momₗ FS m B k
  complete := fun α => by
    have hΔ' : degBound p m B δ < Fintype.card FS.𝕊 := by omega
    obtain ⟨h1, h2, h3, h4⟩ := elemTab_complete (FS := FS) hB hm hΔ' α
    exact ⟨elemTab FS m B α, h1, h2, h3, fun k => h4 k (by have := k.isLt; omega)⟩
  sound := fun y hy hw => by
    obtain ⟨f, hf, hcard⟩ := rep_sound hB hm hΔ y hy hw
    exact ⟨f, fun k => hf k (by have := k.isLt; omega), hcard⟩

end ExplicitTables

open ExplicitTables in
/-- **Theorem A.8** (explicit moment representations), existence form. -/
private theorem exists_explicit_momentRepresentation (p : ℕ) [Fact p.Prime] (S m B : ℕ)
    (hS : 2 ≤ S) (hm : 1 ≤ m) (hB : 2 ≤ B) : Nonempty (ExplicitMomentRepresentation p S m B) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- the degree `δ`: the least power of `p` with `δ ≥ S`
  obtain ⟨e, -, hSδ, hδlt⟩ := exists_pow_between hp hS
  set δ := p ^ e with hδ
  have hδ1 : 1 ≤ δ := by omega
  -- the sample field size `q = p^d`: the least power of `p` with `q ≥ 8 p m B δ`
  have hpos : 0 < p * m * B * δ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  have hN : 2 ≤ 8 * p * m * B * δ := by
    calc 2 ≤ 8 := by norm_num
      _ ≤ 8 * (p * m * B * δ) := Nat.le_mul_of_pos_right 8 hpos
      _ = 8 * p * m * B * δ := by ring
  obtain ⟨d, hd1, hdN, hdlt⟩ := exists_pow_between hp hN
  obtain ⟨FS⟩ := FieldSetup.exists_fieldSetup p d δ hd1 hδ1
  have hq : Fintype.card FS.𝕊 = p ^ d := FS.card_𝕊
  have hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊 := by
    rw [hq]
    refine lt_of_lt_of_le ?_ hdN
    unfold degBound
    have hpm : 0 < 8 * p * m := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hBδ : (B - 1) * (δ - 1) < B * δ :=
      calc (B - 1) * (δ - 1) ≤ (B - 1) * δ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ < B * δ := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    calc 4 * (2 * p * m * (B - 1) * (δ - 1)) = (8 * p * m) * ((B - 1) * (δ - 1)) := by ring
      _ < (8 * p * m) * (B * δ) := (Nat.mul_lt_mul_left hpm).mpr hBδ
      _ = 8 * p * m * B * δ := by ring
  refine ⟨⟨FS.K, encodingTuple FS hSδ, rep FS m B hB hm hΔ, Fintype.card FS.𝕊, rfl, rfl, ?_,
    ⟨d, hd1, hq⟩, ?_, ?_⟩⟩
  · show Fintype.card (Fin m → FS.𝕊) = Fintype.card FS.𝕊 ^ m
    rw [Fintype.card_fun, Fintype.card_fin]
  · calc B ≤ B * (8 * p * m * δ) := Nat.le_mul_of_pos_right B
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
      _ = 8 * p * m * B * δ := by ring
      _ ≤ p ^ d := hdN
      _ = Fintype.card FS.𝕊 := hq.symm
  · calc Fintype.card FS.𝕊 = p ^ d := hq
      _ < p * (8 * p * m * B * δ) := hdlt
      _ = 8 * p ^ 2 * m * B * δ := by ring
      _ ≤ 8 * p ^ 2 * m * B * (p * S) := Nat.mul_le_mul_left _ hδlt.le
      _ = 8 * p ^ 3 * m * S * B := by ring

end LatticePrepro

open LatticePrepro
open Polynomial
open ExplicitTables
theorem solution (p : ℕ) [Fact p.Prime] (S m B : ℕ)
    (hS : 2 ≤ S) (hm : 1 ≤ m) (hB : 2 ≤ B) : Nonempty (ExplicitMomentRepresentation p S m B) :=
  @LatticePrepro.exists_explicit_momentRepresentation p _ S m B hS hm hB
