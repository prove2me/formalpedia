-- Prove2me | solution 1 for HopfAlgebra.FVect.exists_profile_of_isFCompatible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e3eea079-7657-54e5-bb5f-7599194a217b

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_FVect_exists_profile_of_isFCompatible

universe u v

namespace RaynProfileDict

private def wt (p : ℕ) {r : ℕ} (d : Fin r → Fin p) : ℕ := ∑ j : Fin r, p ^ (j : ℕ) * (d j : ℕ)

private theorem ofDigits_ofFn (p : ℕ) : ∀ {n : ℕ} (f : Fin n → ℕ),
    Nat.ofDigits p (List.ofFn f) = ∑ j : Fin n, p ^ (j : ℕ) * f j
  | 0, f => by simp [Nat.ofDigits_nil]
  | n + 1, f => by
    rw [List.ofFn_succ, Nat.ofDigits_cons, ofDigits_ofFn p (fun j => f j.succ), Fin.sum_univ_succ,
      Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private theorem wt_eq_ofDigits (p : ℕ) {r : ℕ} (d : Fin r → Fin p) :
    wt p d = Nat.ofDigits p (List.ofFn fun j => (d j : ℕ)) := by
  unfold wt
  rw [ofDigits_ofFn]

private theorem wt_lt {p : ℕ} (hp : 1 < p) {r : ℕ} (d : Fin r → Fin p) : wt p d < p ^ r := by
  rw [wt_eq_ofDigits]
  have h := Nat.ofDigits_lt_base_pow_length (b := p) (l := List.ofFn fun j => (d j : ℕ)) hp
    (fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact (d j).isLt)
  simpa using h

private theorem wt_single {p : ℕ} [NeZero p] (hp : 1 < p) {r : ℕ} (i : Fin r) :
    wt p (Pi.single i (1 : Fin p)) = p ^ (i : ℕ) := by
  unfold wt
  rw [Finset.sum_eq_single i]
  · simp [Fin.val_one', Nat.mod_eq_of_lt hp]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem eq_single_of_wt {p : ℕ} [NeZero p] (hp : 1 < p) {r : ℕ} (d : Fin r → Fin p) (i : Fin r)
    (h : wt p d = p ^ (i : ℕ)) : d = Pi.single i (1 : Fin p) := by
  have h' : wt p d = wt p (Pi.single i (1 : Fin p)) := by rw [h, wt_single hp]
  rw [wt_eq_ofDigits, wt_eq_ofDigits] at h'
  have hl := Nat.ofDigits_inj_of_len_eq hp (by simp)
    (fun x hx => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact (d j).isLt)
    (fun x hx => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact ((Pi.single i (1 : Fin p) : Fin r → Fin p) j).isLt) h'
  have hf := List.ofFn_injective hl
  funext j
  exact Fin.ext (congrFun hf j)

private theorem isUnit_iff_addVal_eq_zero {R' : Type u} [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] (x : R') :
    IsUnit x ↔ IsDiscreteValuationRing.addVal R' x = 0 := by
  rw [isUnit_iff_dvd_one, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_one]
  exact nonpos_iff_eq_zero

private theorem separate {R' : Type u} [CommRing R'] [IsLocalRing R']
    {p r : ℕ} (hp : p.Prime) {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
    (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R')
    (hχ : ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l)
    {N M : ℕ} (hN0 : 0 < N) (hN : N < p ^ r) (hM0 : 0 < M) (hM : M < p ^ r) (hNM : N ≠ M) :
    ∃ l : Fˣ, IsUnit (((χ l : R'ˣ) : R') ^ N - ((χ l : R'ˣ) : R') ^ M) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : orderOf g = p ^ r - 1 := by
    rw [hg, Nat.card_units, Nat.card_eq_fintype_card, hF]
  have hpow : g ^ N ≠ g ^ M := by
    intro h
    rw [pow_eq_pow_iff_modEq, hcard] at h
    apply hNM
    have h1 : N - 1 ≡ M - 1 [MOD p ^ r - 1] := by
      have hN' : N = (N - 1) + 1 := by omega
      have hM' : M = (M - 1) + 1 := by omega
      rw [hN', hM'] at h
      exact Nat.ModEq.add_right_cancel' 1 h
    have h2 := h1.eq_of_lt_of_lt (by omega) (by omega)
    omega
  refine ⟨g, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hχ, ← map_pow, ← map_pow,
    ← map_sub]
  intro h0
  have h1 : ((g : F) ^ N - (g : F) ^ M) = 0 := ι.injective (by rw [h0, map_zero])
  apply hpow
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact sub_eq_zero.mp h1

private theorem val_ne_zero {p : ℕ} [NeZero p] {x : Fin p} (hx : x ≠ 0) : (x : ℕ) ≠ 0 :=
  fun h => hx (Fin.ext (by simp [h]))

section NormalForm

variable {R' : Type u} [CommRing R'] [IsLocalRing R'] [IsDomain R']
  {p r : ℕ} [NeZero p] (hp : p.Prime)
  {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
  (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R')
  (hχ : ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l)
  {B : Type v} [CommRing B] [HopfAlgebra R' B]
  (act : F → (B →ₐc[R'] B)) (X : Fin r → B)
  (h1 : ∀ i (l : Fˣ), (act l) (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i)
  (b : Module.Basis (Fin r → Fin p) R' B) (hb : ∀ d, b d = ∏ i, X i ^ (d i : ℕ))
  (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)

include hp hb in
private theorem X_eq_basis (i : Fin r) : X i = b (Pi.single i (1 : Fin p)) := by
  rw [hb, Finset.prod_eq_single i]
  · simp [Fin.val_one', Nat.mod_eq_of_lt hp.one_lt]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

include hp hb in
private theorem X_ne_zero (i : Fin r) : X i ≠ 0 := by
  rw [X_eq_basis hp X b hb i]
  exact b.ne_zero _

include hp hb in
private theorem smul_X_inj (i : Fin r) {c c' : R'} (h : c • X i = c' • X i) : c = c' := by
  have h0 : (c - c') • X i = 0 := by rw [sub_smul, h, sub_self]
  rcases b.smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (X_ne_zero hp X b hb i)

include h1 hb in
private theorem act_basis (l : Fˣ) (d : Fin r → Fin p) :
    (act l) (b d) = ((χ l : R'ˣ) : R') ^ wt p d • b d := by
  rw [hb, map_prod]
  simp only [map_pow, h1, smul_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, ← pow_mul]
  rw [Finset.prod_smul, Finset.prod_pow_eq_pow_sum]
  rfl

include hb h5 in
private theorem counit_basis (d : Fin r → Fin p) :
    Coalgebra.counit (R := R') (b d) = if d = 0 then 1 else 0 := by
  have key : ∀ x : B, Coalgebra.counit (R := R') x = Bialgebra.counitAlgHom R' B x := fun _ => rfl
  rw [hb, key, map_prod]
  simp only [map_pow]
  simp only [← key, h5]
  split_ifs with hd
  · subst hd
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hd
    refine Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow (val_ne_zero ?_))
    simpa using hj

include hp hF hχ h1 hb h5 in

private theorem eigen_mem (i : Fin r) (y : B)
    (hy : ∀ l : Fˣ, (act l) y = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • y)
    (hy0 : Coalgebra.counit (R := R') y = 0) : ∃ c : R', y = c • X i := by

  have hcoord : ∀ d, d ≠ Pi.single i (1 : Fin p) → b.repr y d = 0 := by
    intro d hd
    by_cases hd0 : d = 0
    ·
      subst hd0
      have hsum := congrArg (Coalgebra.counit (R := R')) (b.sum_repr y)
      rw [map_sum] at hsum
      simp only [map_smul, counit_basis X b hb h5, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
      rw [hsum, hy0]
    ·
      have hwt0 : 0 < wt p d := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hd0
        have hj' : 0 < (d j : ℕ) := Nat.pos_of_ne_zero (val_ne_zero (by simpa using hj))
        unfold wt
        exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
          ⟨j, Finset.mem_univ _, Nat.mul_pos (pow_pos hp.pos _) hj'⟩
      have hne : wt p d ≠ p ^ (i : ℕ) := fun h => hd (eq_single_of_wt hp.one_lt d i h)
      obtain ⟨l, hl⟩ := separate hp hF χ ι hχ hwt0 (wt_lt hp.one_lt d) (pow_pos hp.pos _)
        (Nat.pow_lt_pow_right hp.one_lt i.isLt) hne

      have hL : (act l) y = ∑ d', (b.repr y d' * ((χ l : R'ˣ) : R') ^ wt p d') • b d' := by
        conv_lhs => rw [← b.sum_repr y]
        rw [map_sum]
        refine Finset.sum_congr rfl fun d' _ => ?_
        rw [map_smul, act_basis χ act X h1 b hb l d', smul_smul]
      have hR : (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • y
          = ∑ d', (((χ l : R'ˣ) : R') ^ (p ^ (i : ℕ)) * b.repr y d') • b d' := by
        conv_lhs => rw [← b.sum_repr y]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun d' _ => ?_
        rw [smul_smul, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
      have hEq := hy l
      rw [hL, hR] at hEq
      have hd' := congrArg (fun v => b.repr v d) hEq
      simp only [b.repr_sum_self] at hd'
      have hmul : b.repr y d * (((χ l : R'ˣ) : R') ^ wt p d - ((χ l : R'ˣ) : R') ^ (p ^ (i : ℕ))) = 0 := by
        rw [mul_sub, hd']
        ring
      exact (hl.mul_left_eq_zero).mp hmul
  refine ⟨b.repr y (Pi.single i (1 : Fin p)), ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.sum_eq_single (Pi.single i (1 : Fin p))]
  · rw [X_eq_basis hp X b hb i]
  · intro d _ hd
    rw [hcoord d hd, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end NormalForm

end RaynProfileDict

open RaynProfileDict in
theorem solution
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [CharZero R']
    (p r : ℕ) [Fact p.Prime] [NeZero r]
    (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
    (hq : IsUnit ((p ^ r : R') - 1))
    (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R')
    (hχ : ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l)
    (B : Type v) [CommRing B] [HopfAlgebra R' B] [Module.Finite R' B] [Module.Free R' B]
    (hrank : Module.finrank R' B = p ^ r)
    (act : F → (B →ₐc[R'] B))
    (act_one : act 1 = BialgHom.id R' B)
    (act_mul : ∀ a b, act (a * b) = (act a).comp (act b))
    (act_add : ∀ a b, ((act (a + b) : B →ₐ[R'] B).toLinearMap) =
      LinearMap.mul' R' B ∘ₗ TensorProduct.map (act a : B →ₐ[R'] B).toLinearMap (act b : B →ₐ[R'] B).toLinearMap
        ∘ₗ Coalgebra.comul)
    (X : Fin r → B) (δ : Fin r → R')
    (h1 : ∀ i (l : Fˣ), (act l) (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i)
    (h2 : ∀ i, X i ^ p = δ i • X (i + 1))
    (b : Module.Basis (Fin r → Fin p) R' B) (hb : ∀ d, b d = ∏ i, X i ^ (d i : ℕ))
    (h4 : ∀ i, δ i ∣ (p : R'))
    (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
    (B' : Type v) [CommRing B'] [HopfAlgebra R' B'] [Module.Finite R' B'] [Module.Free R' B']
    (hrank' : Module.finrank R' B' = p ^ r)
    (act' : F → (B' →ₐc[R'] B'))
    (act_one' : act' 1 = BialgHom.id R' B')
    (act_mul' : ∀ a b, act' (a * b) = (act' a).comp (act' b))
    (act_add' : ∀ a b, ((act' (a + b) : B' →ₐ[R'] B').toLinearMap) =
      LinearMap.mul' R' B' ∘ₗ TensorProduct.map (act' a : B' →ₐ[R'] B').toLinearMap (act' b : B' →ₐ[R'] B').toLinearMap
        ∘ₗ Coalgebra.comul)
    (X' : Fin r → B') (δ' : Fin r → R')
    (h1' : ∀ i (l : Fˣ), (act' l) (X' i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X' i)
    (h2' : ∀ i, X' i ^ p = δ' i • X' (i + 1))
    (b' : Module.Basis (Fin r → Fin p) R' B') (hb' : ∀ d, b' d = ∏ i, X' i ^ (d i : ℕ))
    (h4' : ∀ i, δ' i ∣ (p : R'))
    (h5' : ∀ i, Coalgebra.counit (R := R') (X' i) = 0)
    (u : B →ₐc[R'] B')
    (hu : ∀ l : F, u.comp (act l) = (act' l).comp u)
    (hu_inj : Function.Injective u) :
    ∃ a : Fin r → ℤ, (∀ i, 0 ≤ a i) ∧
      (∀ i, ((IsDiscreteValuationRing.addVal R' (δ i)).toNat : ℤ) =
        p * a i + ((IsDiscreteValuationRing.addVal R' (δ' i)).toNat : ℤ) - a (i + 1)) ∧
      (Function.Bijective u ↔ ∀ i, a i = 0) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have _ := hq; have _ := hrank; have _ := hrank'; have _ := act_one; have _ := act_mul; have _ := act_add
  have _ := act_one'; have _ := act_mul'; have _ := act_add'

  have hu_apply : ∀ (l : F) (x : B), (act' l) (u x) = u ((act l) x) := by
    intro l x
    have h := DFunLike.congr_fun (hu l) x
    rw [BialgHom.coe_comp, BialgHom.coe_comp] at h
    exact (h).symm

  have hR1 : ∀ i, ∃ c : R', u (X i) = c • X' i := by
    intro i
    refine eigen_mem hp hF χ ι hχ act' X' h1' b' hb' h5' i (u (X i)) (fun l => ?_) ?_
    · rw [hu_apply, h1, map_smul]
    · rw [CoalgHomClass.counit_comp_apply, h5]
  choose c hc using hR1
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h0
    apply X_ne_zero hp X b hb i
    apply hu_inj
    rw [hc, h0, zero_smul, map_zero]

  have hkey : ∀ i, c i ^ p * δ' i = δ i * c (i + 1) := by
    intro i
    apply smul_X_inj hp X' b' hb' (i + 1)
    have h := congrArg u (h2 i)
    rw [map_pow, map_smul, hc, hc, smul_pow, h2', smul_smul, smul_smul] at h
    exact h

  have hδ0 : ∀ i, δ i ≠ 0 := fun i h => by
    have := h4 i
    rw [h] at this
    exact hp.ne_zero (by exact_mod_cast zero_dvd_iff.mp this)
  have hδ0' : ∀ i, δ' i ≠ 0 := fun i h => by
    have := h4' i
    rw [h] at this
    exact hp.ne_zero (by exact_mod_cast zero_dvd_iff.mp this)
  have hfin : ∀ x : R', x ≠ 0 → ∃ n : ℕ, IsDiscreteValuationRing.addVal R' x = n := by
    intro x hx
    have h := mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hx
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    exact ⟨n, hn.symm⟩
  choose n hn using fun i => hfin (c i) (hc0 i)
  choose m hm using fun i => hfin (δ i) (hδ0 i)
  choose m' hm' using fun i => hfin (δ' i) (hδ0' i)
  have hlaw : ∀ i, p * n i + m' i = m i + n (i + 1) := by
    intro i
    have h := congrArg (IsDiscreteValuationRing.addVal R') (hkey i)
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, hn, hm', hm, hn, nsmul_eq_mul] at h
    exact_mod_cast h

  have hcrit : Function.Bijective u ↔ ∀ i, IsUnit (c i) := by
    constructor
    · rintro ⟨-, hsurj⟩ i
      obtain ⟨y, hy⟩ := hsurj (X' i)
      have hy_eig : ∀ l : Fˣ, (act l) y = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • y := by
        intro l
        apply hu_inj
        rw [← hu_apply, hy, h1', map_smul, hy]
      have hy0 : Coalgebra.counit (R := R') y = 0 := by
        have h := h5' i
        rw [← hy, CoalgHomClass.counit_comp_apply] at h
        exact h
      obtain ⟨γ, hγ⟩ := eigen_mem hp hF χ ι hχ act X h1 b hb h5 i y hy_eig hy0
      have h : (γ * c i) • X' i = X' i := by
        rw [← smul_smul, ← hc i, ← map_smul u, ← hγ, hy]
      have h' : (γ * c i) • X' i = (1 : R') • X' i := by rw [one_smul]; exact h
      have h'' := smul_X_inj hp X' b' hb' i h'
      exact isUnit_iff_dvd_one.mpr (Dvd.intro γ (by rw [mul_comm]; exact h''))
    · intro hunit
      refine ⟨hu_inj, ?_⟩

      have hX' : ∀ i, ∃ y : B, u y = X' i := by
        intro i
        obtain ⟨w, hw⟩ := hunit i
        refine ⟨((w⁻¹ : R'ˣ) : R') • X i, ?_⟩
        rw [map_smul, hc, ← hw, smul_smul, Units.inv_mul, one_smul]
      choose y hy using hX'

      intro z
      refine ⟨∑ d, b'.repr z d • ∏ j, y j ^ (d j : ℕ), ?_⟩
      rw [map_sum]
      conv_rhs => rw [← b'.sum_repr z]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_smul, map_prod, hb' d]
      simp only [map_pow, hy]
  refine ⟨fun i => (n i : ℤ), fun i => by dsimp only; exact_mod_cast Nat.zero_le (n i), fun i => ?_, ?_⟩
  · dsimp only
    rw [hm, hm', ENat.toNat_coe, ENat.toNat_coe]
    have h : ((p : ℤ) * n i + m' i : ℤ) = m i + n (i + 1) := by exact_mod_cast hlaw i
    linarith
  · dsimp only
    rw [hcrit]
    refine forall_congr' fun i => ?_
    rw [isUnit_iff_addVal_eq_zero, hn]
    simp only [Nat.cast_eq_zero]

end S_HopfAlgebra_FVect_exists_profile_of_isFCompatible
end P2MW
export P2MW.S_HopfAlgebra_FVect_exists_profile_of_isFCompatible (solution)
