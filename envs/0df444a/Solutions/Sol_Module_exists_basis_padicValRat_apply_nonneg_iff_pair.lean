-- Prove2me | solution 1 for Module.exists_basis_padicValRat_apply_nonneg_iff_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/eae9acec-8321-5958-9da8-a9d295000464

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair

set_option autoImplicit false

namespace PadicLattice

variable (p : ℕ) [Fact p.Prime]

def intSubring : Subring ℚ where
  carrier := {x | 0 ≤ padicValRat p x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    by_cases hxy : x + y = 0
    · rw [hxy, padicValRat.zero]
    · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add hxy)
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rwa [padicValRat.neg]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    by_cases hx0 : x = 0
    · rw [hx0, zero_mul, padicValRat.zero]
    by_cases hy0 : y = 0
    · rw [hy0, mul_zero, padicValRat.zero]
    rw [padicValRat.mul hx0 hy0]
    exact add_nonneg hx hy

variable {p}

theorem mem_intSubring_iff {x : ℚ} : x ∈ intSubring p ↔ 0 ≤ padicValRat p x := Iff.rfl

theorem pow_mem_intSubring (n : ℕ) : (p : ℚ) ^ n ∈ intSubring p := by
  rw [mem_intSubring_iff]
  have hp : (Fact.out : p.Prime).one_lt = (Fact.out : p.Prime).one_lt := rfl
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [padicValRat.pow _, padicValRat.self (Fact.out : p.Prime).one_lt]
  simp

theorem inv_mem_intSubring_of_padicValRat_eq_zero {x : ℚ} (hx : padicValRat p x = 0) : x⁻¹ ∈ intSubring p := by
  rw [mem_intSubring_iff, padicValRat.inv, hx, neg_zero]

theorem exists_unit_mul_pow_eq {x : ℚ} (hx : x ∈ intSubring p) (hx0 : x ≠ 0) :
    ∃ (u : (intSubring p)ˣ) (n : ℕ), ((u : intSubring p) : ℚ) * (p : ℚ) ^ n = x := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = padicValRat p x := ⟨(padicValRat p x).toNat, Int.toNat_of_nonneg hx⟩
  set y : ℚ := x * ((p : ℚ) ^ n)⁻¹ with hy
  have hy0 : y ≠ 0 := mul_ne_zero hx0 (inv_ne_zero (pow_ne_zero _ hpq))
  have hvy : padicValRat p y = 0 := by
    rw [hy, padicValRat.mul hx0 (inv_ne_zero (pow_ne_zero _ hpq)), padicValRat.inv, padicValRat.pow _,
      padicValRat.self (Fact.out : p.Prime).one_lt, ← hn]
    ring
  have hymem : y ∈ intSubring p := by rw [mem_intSubring_iff, hvy]
  have hyinv : y⁻¹ ∈ intSubring p := inv_mem_intSubring_of_padicValRat_eq_zero hvy
  refine ⟨⟨⟨y, hymem⟩, ⟨y⁻¹, hyinv⟩, Subtype.ext (mul_inv_cancel₀ hy0), Subtype.ext (inv_mul_cancel₀ hy0)⟩, n, ?_⟩
  show y * (p : ℚ) ^ n = x
  rw [hy, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hpq), mul_one]

scoped instance : IsPrincipalIdealRing (intSubring p) := by
  classical
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact ⟨⟨0, by simp⟩⟩

  have hex : ∃ n : ℕ, ∃ x ∈ I, x ≠ 0 ∧ padicValRat p (x : ℚ) = n := by
    obtain ⟨x, hxI, hx0⟩ := I.ne_bot_iff.mp hI
    have hxq0 : (x : ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨u, n, hun⟩ := exists_unit_mul_pow_eq x.2 hxq0
    refine ⟨n, x, hxI, hx0, ?_⟩
    rw [← hun, padicValRat.mul (fun h => (u.isUnit.ne_zero (Subtype.ext h))) (pow_ne_zero _ hpq),
      padicValRat.pow _, padicValRat.self (Fact.out : p.Prime).one_lt]
    have hu0 : ((u : intSubring p) : ℚ) ≠ 0 := fun h => u.isUnit.ne_zero (Subtype.ext h)
    have hvu : padicValRat p ((u : intSubring p) : ℚ) = 0 := by
      apply le_antisymm _ (u : intSubring p).2
      have h1 := ((u⁻¹ : (intSubring p)ˣ) : intSubring p).2
      rw [mem_intSubring_iff] at h1
      have hprod : ((u : intSubring p) : ℚ) * ((u⁻¹ : (intSubring p)ˣ) : intSubring p) = 1 := by
        have h := congrArg Subtype.val u.mul_inv
        rwa [MulMemClass.coe_mul, OneMemClass.coe_one] at h
      have hinv0 : (((u⁻¹ : (intSubring p)ˣ) : intSubring p) : ℚ) ≠ 0 := fun h => by
        rw [h, mul_zero] at hprod; exact zero_ne_one hprod
      have hm := padicValRat.mul (p := p) hu0 hinv0
      rw [hprod, padicValRat.one] at hm
      linarith
    rw [hvu]
    simp
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ I, y ≠ 0 → (Nat.find hex : ℤ) ≤ padicValRat p (y : ℚ) := by
    intro y hyI hy0
    have hyq0 : (y : ℚ) ≠ 0 := fun h => hy0 (Subtype.ext h)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = padicValRat p (y : ℚ) := ⟨_, Int.toNat_of_nonneg y.2⟩
    have : Nat.find hex ≤ m := Nat.find_min' hex ⟨y, hyI, hy0, hm.symm⟩
    rw [← hm]
    exact_mod_cast this
  refine ⟨⟨x, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hxI)⟩⟩
  intro y hyI
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_mem _
  have hxq0 : (x : ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hyq0 : (y : ℚ) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hquot : (y : ℚ) / x ∈ intSubring p := by
    rw [mem_intSubring_iff, padicValRat.div hyq0 hxq0, hxn]
    linarith [hmin y hyI hy0]
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨(y : ℚ) / x, hquot⟩, Subtype.ext ?_⟩
  show (y : ℚ) / x * x = y
  rw [div_mul_cancel₀ _ hxq0]

end PadicLattice
p2m_reactivate "P2MW.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair.PadicLattice"

namespace PadicLattice

variable {p : ℕ} [Fact p.Prime]
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

def lattice (p : ℕ) [Fact p.Prime] (a : ℤ → M →ₗ[ℚ] ℚ) : Submodule (intSubring p) M where
  carrier := {x | ∀ m, a m x ∈ intSubring p}
  zero_mem' := fun m => by rw [map_zero]; exact zero_mem _
  add_mem' := fun {x y} hx hy m => by rw [map_add]; exact add_mem (hx m) (hy m)
  smul_mem' := fun r x hx m => by
    rw [show (r • x : M) = ((r : ℚ) • x) from rfl, map_smul, smul_eq_mul]
    exact mul_mem r.2 (hx m)

theorem mem_lattice_iff {a : ℤ → M →ₗ[ℚ] ℚ} {x : M} : x ∈ lattice p a ↔ ∀ m, a m x ∈ intSubring p := Iff.rfl

theorem exists_finset_forall_eq_zero [FiniteDimensional ℚ M] (a : ℤ → M →ₗ[ℚ] ℚ)
    (hinj : ∀ x, (∀ m, a m x = 0) → x = 0) :
    ∃ S : Finset ℤ, ∀ x : M, (∀ m ∈ S, a m x = 0) → x = 0 := by
  classical
  let K : Finset ℤ → Submodule ℚ M := fun S => ⨅ m ∈ S, LinearMap.ker (a m)
  have hK : ∀ S x, x ∈ K S ↔ ∀ m ∈ S, a m x = 0 := by
    intro S x
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker]
  have hmono : ∀ S T, S ⊆ T → K T ≤ K S := by
    intro S T hST x hx
    rw [hK] at hx ⊢
    exact fun m hm => hx m (hST hm)
  have hex : ∃ d : ℕ, ∃ S : Finset ℤ, Module.finrank ℚ (K S) = d := ⟨_, ∅, rfl⟩
  obtain ⟨S₀, hS₀⟩ := Nat.find_spec hex
  refine ⟨S₀, fun x hx => hinj x fun m => ?_⟩
  have hle : K (insert m S₀) ≤ K S₀ := hmono _ _ (Finset.subset_insert m S₀)
  have hge : Module.finrank ℚ (K S₀) ≤ Module.finrank ℚ (K (insert m S₀)) := by
    rw [hS₀]
    exact Nat.find_min' hex ⟨insert m S₀, rfl⟩
  have heq : K (insert m S₀) = K S₀ := Submodule.eq_of_le_of_finrank_le hle hge
  have hx' : x ∈ K (insert m S₀) := by rw [heq, hK]; exact hx
  rw [hK] at hx'
  exact hx' m (Finset.mem_insert_self m S₀)

theorem exists_latticeBasis [FiniteDimensional ℚ M] (p : ℕ) [Fact p.Prime]
    (a : ℤ → M →ₗ[ℚ] ℚ) (hinj : ∀ x, (∀ m, a m x = 0) → x = 0) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (intSubring p) ↥(lattice p a)) := by
  classical
  have hp : p.Prime := Fact.out
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set r := Module.finrank ℚ M
  let e : Module.Basis (Fin r) ℚ M := Module.finBasis ℚ M
  obtain ⟨S, hS⟩ := exists_finset_forall_eq_zero a hinj
  let T : M →ₗ[ℚ] (S → ℚ) := LinearMap.pi fun s => a s.1
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hS x
    intro m hm
    have := congrFun hx ⟨m, hm⟩
    simpa [T] using this
  obtain ⟨g, hg⟩ := T.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hT)
  let coord : Fin r → M →ₗ[ℚ] ℚ := fun i => (e.coord i)
  have hfac : ∀ i x, coord i x = ∑ s : S, (e.coord i (g (Pi.single s 1))) * a s.1 x := by
    intro i x
    have hx : x = g (T x) := by
      have := congrArg (fun f => f x) hg
      simpa using this.symm
    conv_lhs => rw [hx]
    have hTx : T x = ∑ s : S, a s.1 x • (Pi.single s (1 : ℚ) : S → ℚ) := by
      ext s
      simp [T, Finset.sum_apply, Pi.single_apply]
    rw [hTx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  have hmat : ∃ N : ℕ, ∀ i (s : S), 0 ≤ padicValRat p ((p : ℚ) ^ N * e.coord i (g (Pi.single s 1))) := by
    have : ∀ i (s : S), ∃ N : ℕ, 0 ≤ padicValRat p ((p : ℚ) ^ N * e.coord i (g (Pi.single s 1))) := by
      intro i s
      set y := e.coord i (g (Pi.single s 1))
      by_cases hy : y = 0
      · exact ⟨0, by rw [hy, mul_zero, padicValRat.zero]⟩
      refine ⟨(-(padicValRat p y)).toNat, ?_⟩
      rw [padicValRat.mul (pow_ne_zero _ hpq) hy, padicValRat.pow _, padicValRat.self hp.one_lt]
      have := Int.self_le_toNat (-(padicValRat p y))
      push_cast
      omega
    choose Nf hNf using this
    refine ⟨Finset.univ.sup fun is : Fin r × S => Nf is.1 is.2, fun i s => ?_⟩
    have hle : Nf i s ≤ Finset.univ.sup fun is : Fin r × S => Nf is.1 is.2 :=
      Finset.le_sup (f := fun is : Fin r × S => Nf is.1 is.2) (Finset.mem_univ (i, s))
    set y := e.coord i (g (Pi.single s 1))
    by_cases hy : y = 0
    · rw [hy, mul_zero, padicValRat.zero]
    have h0 := hNf i s
    rw [padicValRat.mul (pow_ne_zero _ hpq) hy, padicValRat.pow _, padicValRat.self hp.one_lt] at h0 ⊢
    have : ((Nf i s : ℕ) : ℤ) ≤ (Finset.univ.sup fun is : Fin r × S => Nf is.1 is.2 : ℕ) := by exact_mod_cast hle
    linarith
  obtain ⟨N₁, hN₁⟩ := hmat
  have hcoordΛ : ∀ x ∈ lattice p a, ∀ i, (p : ℚ) ^ N₁ * coord i x ∈ intSubring p := by
    intro x hx i
    rw [hfac, Finset.mul_sum]
    refine sum_mem fun s _ => ?_
    rw [← mul_assoc]
    exact mul_mem (hN₁ i s) (hx s.1)
  let Φ : ↥(lattice p a) →ₗ[intSubring p] (Fin r → intSubring p) :=
    { toFun := fun x i => ⟨(p : ℚ) ^ N₁ * coord i x, hcoordΛ x x.2 i⟩
      map_add' := fun x y => by
        ext i
        simp only [Submodule.coe_add, map_add, Pi.add_apply, Subring.coe_add]
        ring
      map_smul' := fun c x => by
        ext i
        simp only [Submodule.coe_smul_of_tower, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
        rw [show ((c • (x : M)) : M) = ((c : ℚ) • (x : M)) from rfl, map_smul, smul_eq_mul]
        ring }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply e.ext_elem
    intro i
    have h := congrArg (fun v : Fin r → intSubring p => ((v i : intSubring p) : ℚ)) hxy
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h
    have h' := mul_left_cancel₀ (pow_ne_zero N₁ hpq) h
    exact h'
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun (intSubring p) (Fin r)) (LinearMap.range Φ)
  exact ⟨n, ⟨bN.map (LinearEquiv.ofInjective Φ hΦ).symm⟩⟩

theorem exists_basis_of_latticeBasis (p : ℕ) [Fact p.Prime] (a : ℤ → M →ₗ[ℚ] ℚ)
    (hbd : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x))
    {n : ℕ} (bΛ : Module.Basis (Fin n) (intSubring p) ↥(lattice p a)) :
    ∃ b : Module.Basis (Fin n) ℚ M, (∀ i, b i = (bΛ i : M)) ∧
      ∀ c : Fin n → ℚ, (∑ i, c i • b i) ∈ lattice p a ↔ ∀ i, c i ∈ intSubring p := by
  classical
  have hp : p.Prime := Fact.out
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let v : Fin n → M := fun i => (bΛ i : M)
  have hscale : ∀ x : M, ∃ N : ℕ, ((p : ℚ) ^ N) • x ∈ lattice p a := by
    intro x
    obtain ⟨N, hN⟩ := hbd x
    exact ⟨N, fun m => by rw [map_smul, smul_eq_mul]; exact hN m⟩
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hden : ∃ N : ℕ, ∀ j, (p : ℚ) ^ N * c j ∈ intSubring p := by
      have : ∀ j, ∃ N : ℕ, (p : ℚ) ^ N * c j ∈ intSubring p := by
        intro j
        by_cases hcj : c j = 0
        · exact ⟨0, by rw [hcj, mul_zero]; exact zero_mem _⟩
        refine ⟨(-(padicValRat p (c j))).toNat, ?_⟩
        rw [mem_intSubring_iff, padicValRat.mul (pow_ne_zero _ hpq) hcj, padicValRat.pow _,
          padicValRat.self hp.one_lt]
        have := Int.self_le_toNat (-(padicValRat p (c j)))
        push_cast
        omega
      choose Nf hNf using this
      refine ⟨Finset.univ.sup Nf, fun j => ?_⟩
      have hle : Nf j ≤ Finset.univ.sup Nf := Finset.le_sup (Finset.mem_univ j)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add, mul_comm ((p : ℚ) ^ Nf j), mul_assoc]
      exact mul_mem (pow_mem_intSubring d) (hNf j)
    obtain ⟨N, hN⟩ := hden
    have hrel : ∑ j, (⟨(p : ℚ) ^ N * c j, hN j⟩ : intSubring p) • bΛ j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      have : ∑ j, (((⟨(p : ℚ) ^ N * c j, hN j⟩ : intSubring p) • bΛ j : ↥(lattice p a)) : M)
          = ((p : ℚ) ^ N) • ∑ j, c j • v j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Submodule.coe_smul_of_tower, smul_smul]
        rfl
      rw [this, hc, smul_zero]
    have hzero := Fintype.linearIndependent_iff.mp bΛ.linearIndependent _ hrel i
    have : (p : ℚ) ^ N * c i = 0 := congrArg Subtype.val hzero
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hpq)
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    intro x _
    obtain ⟨N, hN⟩ := hscale x
    have hrepr := bΛ.sum_repr ⟨_, hN⟩
    have hx : x = ((p : ℚ) ^ N)⁻¹ • ∑ j, ((bΛ.repr ⟨_, hN⟩ j : intSubring p) : ℚ) • v j := by
      have h1 : (((p : ℚ) ^ N) • x : M) = ∑ j, ((bΛ.repr ⟨_, hN⟩ j : intSubring p) : ℚ) • v j := by
        have := congrArg (fun y : ↥(lattice p a) => (y : M)) hrepr
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
        exact this.symm
      rw [← h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hpq), one_smul]
    rw [hx]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b : Module.Basis (Fin n) ℚ M := Module.Basis.mk hli hspan
  have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hspan i
  refine ⟨b, hb, fun c => ?_⟩
  constructor
  · intro hx i
    set d : Fin n → ℚ := fun j => ((bΛ.repr ⟨_, hx⟩ j : intSubring p) : ℚ) with hd
    have hsum : ∑ j, d j • b j = ∑ j, c j • b j := by
      have := congrArg (fun y : ↥(lattice p a) => (y : M)) (bΛ.sum_repr ⟨_, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb]
      rfl
    have hcd : c = d := by
      have h1 : b.equivFun.symm c = b.equivFun.symm d := by
        rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, hsum]
      exact b.equivFun.symm.injective h1
    rw [hcd]
    exact (bΛ.repr ⟨_, hx⟩ i).2
  · intro hc
    refine Submodule.sum_mem _ fun j _ => ?_
    have : c j • b j = ((⟨c j, hc j⟩ : intSubring p) • (bΛ j) : ↥(lattice p a)) := by
      rw [Submodule.coe_smul_of_tower, hb]
      rfl
    rw [this]
    exact SetLike.coe_mem _

theorem exists_basis_forall_padicValRat_nonneg_iff [FiniteDimensional ℚ M] (p : ℕ) [Fact p.Prime]
    (a : ℤ → M →ₗ[ℚ] ℚ) (hinj : ∀ x, (∀ m, a m x = 0) → x = 0)
    (hbd : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ M), ∀ c : Fin n → ℚ,
      (∀ m, 0 ≤ padicValRat p (a m (∑ i, c i • b i))) ↔ ∀ i, 0 ≤ padicValRat p (c i) := by
  obtain ⟨n, ⟨bΛ⟩⟩ := exists_latticeBasis p a hinj
  obtain ⟨b, -, hb⟩ := exists_basis_of_latticeBasis p a hbd bΛ
  exact ⟨n, b, fun c => hb c⟩

end PadicLattice
p2m_reactivate "P2MW.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair.PadicLattice"

namespace PadicLattice

theorem exists_basis_update {ι R N : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R N) (v : N) (i₀ : ι) (hu : IsUnit (b.repr v i₀)) :
    ∃ b' : Module.Basis ι R N, b' i₀ = v ∧ ∀ i, i ≠ i₀ → b' i = b i := by
  classical
  set r : ι → R := fun i => b.repr v i with hr
  obtain ⟨w₀, hw₀⟩ := hu
  have hw₀' : (w₀ : R) = r i₀ := hw₀
  have hv : v = ∑ i, r i • b i := (b.sum_repr v).symm
  let w : ι → N := Function.update b i₀ v
  have hw_i₀ : w i₀ = v := Function.update_self i₀ v b
  have hw_ne : ∀ i, i ≠ i₀ → w i = b i := fun i hi => Function.update_of_ne hi v b

  have hsplit : v = r i₀ • b i₀ + ∑ i ∈ Finset.univ.erase i₀, r i • w i := by
    rw [hv, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hw_ne i (Finset.ne_of_mem_erase hi)]
  have hspan : ⊤ ≤ Submodule.span R (Set.range w) := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = i₀
    · subst hi
      have hrest : ∑ j ∈ Finset.univ.erase i, r j • w j ∈ Submodule.span R (Set.range w) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      have hvmem : v ∈ Submodule.span R (Set.range w) := Submodule.subset_span ⟨i, hw_i₀⟩
      have hb : b i = ((w₀⁻¹ : Rˣ) : R) • (v - ∑ j ∈ Finset.univ.erase i, r j • w j) := by
        have h1 : v - ∑ j ∈ Finset.univ.erase i, r j • w j = r i • b i := by
          rw [hsplit]; abel
        rw [h1, smul_smul, ← hw₀', Units.inv_mul, one_smul]
      rw [hb]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hvmem hrest)
    · exact Submodule.subset_span ⟨i, hw_ne i hi⟩
  have hli : LinearIndependent R w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc

    have h1 : ∑ j, c j • w j = c i₀ • v + ∑ j ∈ Finset.univ.erase i₀, c j • b j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hw_i₀]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hw_ne j (Finset.ne_of_mem_erase hj)]
    have hA : c i₀ • v = ∑ j, (c i₀ * r j) • b j := by
      rw [hv, Finset.smul_sum]
      exact Finset.sum_congr rfl (fun j _ => smul_smul _ _ _)
    have hB : ∑ j ∈ Finset.univ.erase i₀, c j • b j = ∑ j, (if j = i₀ then 0 else c j) • b j := by
      rw [← Finset.add_sum_erase _ (fun j => (if j = i₀ then 0 else c j) • b j) (Finset.mem_univ i₀),
        if_pos rfl, zero_smul, zero_add]
      exact Finset.sum_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])
    have hrel : ∑ j, (c i₀ * r j + (if j = i₀ then 0 else c j)) • b j = 0 := by
      rw [h1, hA, hB, ← Finset.sum_add_distrib] at hc
      rw [← hc]
      exact Finset.sum_congr rfl (fun j _ => add_smul _ _ _)
    have hcoef := Fintype.linearIndependent_iff.mp b.linearIndependent _ hrel
    have hci₀ : c i₀ = 0 := by
      have h := hcoef i₀
      rw [if_pos rfl, add_zero] at h
      have : c i₀ * r i₀ * ((w₀⁻¹ : Rˣ) : R) = 0 := by rw [h, zero_mul]
      rwa [mul_assoc, ← hw₀', Units.mul_inv, mul_one] at this
    intro i
    by_cases hi : i = i₀
    · rw [hi]; exact hci₀
    · have h := hcoef i
      rw [if_neg hi, hci₀, zero_mul, zero_add] at h
      exact h
  refine ⟨Module.Basis.mk hli hspan, ?_, ?_⟩
  · rw [Module.Basis.mk_apply]; exact hw_i₀
  · intro i hi
    rw [Module.Basis.mk_apply]; exact hw_ne i hi

variable {p : ℕ} [Fact p.Prime]

theorem isUnit_iff {x : intSubring p} : IsUnit x ↔ (x : ℚ) ≠ 0 ∧ padicValRat p (x : ℚ) = 0 := by
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := hx
    have hprod : ((u : intSubring p) : ℚ) * ((u⁻¹ : (intSubring p)ˣ) : intSubring p) = 1 := by
      have h := congrArg Subtype.val u.mul_inv
      rwa [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    have hu0 : ((u : intSubring p) : ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hprod; exact zero_ne_one hprod
    have hinv0 : (((u⁻¹ : (intSubring p)ˣ) : intSubring p) : ℚ) ≠ 0 := fun h => by
      rw [h, mul_zero] at hprod; exact zero_ne_one hprod
    refine ⟨hu0, le_antisymm ?_ (u : intSubring p).2⟩
    have h1 := ((u⁻¹ : (intSubring p)ˣ) : intSubring p).2
    rw [mem_intSubring_iff] at h1
    have hm := padicValRat.mul (p := p) hu0 hinv0
    rw [hprod, padicValRat.one] at hm
    linarith
  · rintro ⟨hx0, hv⟩
    have hinv : (x : ℚ)⁻¹ ∈ intSubring p := inv_mem_intSubring_of_padicValRat_eq_zero hv
    exact ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem exists_eq_p_mul_of_not_isUnit {x : intSubring p} (hx : ¬ IsUnit x) :
    ∃ y : intSubring p, (x : ℚ) = p * y := by
  have hp : p.Prime := Fact.out
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hx0 : (x : ℚ) = 0
  · exact ⟨0, by rw [hx0]; simp⟩
  have hv : padicValRat p (x : ℚ) ≠ 0 := fun h => hx (isUnit_iff.mpr ⟨hx0, h⟩)
  have hv1 : 1 ≤ padicValRat p (x : ℚ) := by
    have := x.2; rw [mem_intSubring_iff] at this; omega
  refine ⟨⟨(x : ℚ) / p, ?_⟩, ?_⟩
  · rw [mem_intSubring_iff, padicValRat.div hx0 hpq, padicValRat.self hp.one_lt]
    linarith
  · show (x : ℚ) = p * ((x : ℚ) / p)
    rw [mul_div_cancel₀ _ hpq]

end PadicLattice
p2m_reactivate "P2MW.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair.PadicLattice"

namespace PadicLattice

variable {p : ℕ} [Fact p.Prime]
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

set_option maxHeartbeats 3200000 in

theorem exists_basis_pair [FiniteDimensional ℚ M] (p : ℕ) [Fact p.Prime]
    (a a' : ℤ → M →ₗ[ℚ] ℚ) (hinj' : ∀ x, (∀ m, a' m x = 0) → x = 0)
    (hbd : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x))
    (hbd' : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a' m x))
    (hsub : ∀ x, (∀ m, 0 ≤ padicValRat p (a m x)) → ∀ m, 0 ≤ padicValRat p (a' m x))
    (u : M) (hu : ∀ m, 0 ≤ padicValRat p (a m u))
    (hprim : ∃ m, a' m u ≠ 0 ∧ padicValRat p (a' m u) = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ M) (e : Fin n → ℕ) (i₀ : Fin n), b i₀ = u ∧ e i₀ = 0 ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a m (∑ i, c i • b i))) ↔ ∀ i, 0 ≤ padicValRat p (c i)) ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a' m (∑ i, c i • b i))) ↔
        ∀ i, -(e i : ℤ) ≤ padicValRat p (c i)) := by
  classical
  have hp : p.Prime := Fact.out
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero

  set O := lattice p a' with hO
  set Λ := lattice p a with hΛ
  have hΛO : Λ ≤ O := fun x hx m => hsub x hx m
  obtain ⟨n, ⟨β'⟩⟩ := exists_latticeBasis p a' hinj'
  haveI : Module.Finite (intSubring p) ↥O := Module.Finite.of_basis β'
  let N : Submodule (intSubring p) ↥O := Submodule.comap O.subtype Λ

  set pK : ℕ → intSubring p := fun K => ⟨(p : ℚ) ^ K, pow_mem_intSubring K⟩ with hpK
  have hK : ∃ K : ℕ, ∀ j, (pK K • β' j : ↥O) ∈ N := by
    have : ∀ j, ∃ K : ℕ, (pK K • β' j : ↥O) ∈ N := by
      intro j
      obtain ⟨K, hK⟩ := hbd (β' j : M)
      exact ⟨K, fun m => by
        show 0 ≤ padicValRat p (a m (((p : ℚ) ^ K) • ((β' j : ↥O) : M)))
        rw [map_smul, smul_eq_mul]
        exact hK m⟩
    choose Kf hKf using this
    refine ⟨Finset.univ.sup Kf, fun j => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := Kf) (Finset.mem_univ j))
    have : (pK (Finset.univ.sup Kf) • β' j : ↥O) = pK d • (pK (Kf j) • β' j) := by
      rw [smul_smul]
      congr 1
      apply Subtype.ext
      show (p : ℚ) ^ Finset.univ.sup Kf = (p : ℚ) ^ d * (p : ℚ) ^ Kf j
      rw [hd, pow_add, mul_comm]
    rw [this]
    exact N.smul_mem _ (hKf j)
  obtain ⟨K, hKN⟩ := hK
  have hrank : Module.finrank (intSubring p) ↥N = Module.finrank (intSubring p) ↥O := by
    apply le_antisymm (Submodule.finrank_le N)
    let φ : ↥O →ₗ[intSubring p] ↥O := pK K • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h : ((p : ℚ) ^ K) • (x : M) = ((p : ℚ) ^ K) • (y : M) := by
        have := congrArg (fun z : ↥O => (z : M)) hxy
        simpa [φ, hpK, Subring.smul_def] using this
      exact Subtype.ext (smul_right_injective M (pow_ne_zero K hpq) h)
    have hle : LinearMap.range φ ≤ N := by
      rintro _ ⟨x, rfl⟩
      have hx : φ x = ∑ j, β'.repr x j • (pK K • β' j) := by
        show pK K • x = _
        conv_lhs => rw [← β'.sum_repr x]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [smul_comm])
      rw [hx]
      exact N.sum_mem (fun j _ => N.smul_mem _ (hKN j))
    calc Module.finrank (intSubring p) ↥O
        = Module.finrank (intSubring p) ↥(LinearMap.range φ) := (LinearMap.finrank_range_of_inj hφ).symm
      _ ≤ Module.finrank (intSubring p) ↥N := Submodule.finrank_mono hle

  let top := Submodule.smithNormalFormTopBasis β' hrank
  let bot := Submodule.smithNormalFormBotBasis β' hrank
  let coe := Submodule.smithNormalFormCoeffs β' hrank
  have hsnf : ∀ i, ((bot i : ↥N) : ↥O) = coe i • top i := Submodule.smithNormalFormBotBasis_def β' hrank
  have hcoe0 : ∀ i, coe i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero β' hrank

  let γ₀ : Module.Basis (Fin n) (intSubring p) ↥Λ := bot.map (Submodule.comapSubtypeEquivOfLe hΛO)
  have hγ₀ : ∀ i, ((γ₀ i : ↥Λ) : M) = ((coe i : intSubring p) : ℚ) • ((top i : ↥O) : M) := fun i => by
    show (((bot i : ↥N) : ↥O) : M) = _
    rw [hsnf, Submodule.coe_smul_of_tower]
    rfl

  let uO : ↥O := ⟨u, fun m => hsub u hu m⟩
  let uΛ : ↥Λ := ⟨u, hu⟩
  set s : Fin n → intSubring p := fun i => γ₀.repr uΛ i with hs
  have hus : uO = ∑ i, (s i * coe i) • top i := by
    apply Subtype.ext
    have h := congrArg (fun x : ↥Λ => (x : M)) (γ₀.sum_repr uΛ)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
    rw [Submodule.coe_sum]
    have h' : (∑ x, γ₀.repr uΛ x • ((γ₀ x : ↥Λ) : M)) = u := h
    show u = _
    rw [← h']
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hγ₀, Submodule.coe_smul_of_tower,
      show ((γ₀.repr uΛ i • ((((coe i : intSubring p) : ℚ) • ((top i : ↥O) : M)) : M)) : M)
        = ((γ₀.repr uΛ i : intSubring p) : ℚ) • ((((coe i : intSubring p) : ℚ) • ((top i : ↥O) : M)) : M) from rfl,
      smul_smul]
    rfl
  have hr : ∀ i, top.repr uO i = s i * coe i := by
    intro i
    have h1 : top.equivFun uO = fun i => s i * coe i := by
      rw [hus, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    exact congrFun h1 i

  have hunit : ∃ i₀, IsUnit (top.repr uO i₀) := by
    by_contra hall
    push_neg at hall
    choose y hy using fun i => exists_eq_p_mul_of_not_isUnit (hall i)
    let w : ↥O := ∑ i, y i • top i
    have huw : u = (p : ℚ) • (w : M) := by
      have h := congrArg (fun x : ↥O => (x : M)) (top.sum_repr uO)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
      rw [show (uO : M) = u from rfl] at h
      rw [← h, Submodule.coe_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Submodule.coe_smul_of_tower, show ((top.repr uO i • ((top i : ↥O) : M)) : M)
        = ((top.repr uO i : intSubring p) : ℚ) • ((top i : ↥O) : M) from rfl, hy i, ← smul_smul]
      rfl
    obtain ⟨m, hm0, hmv⟩ := hprim
    have hw : 0 ≤ padicValRat p (a' m (w : M)) := (w : ↥O).2 m
    rw [huw, map_smul, smul_eq_mul] at hm0 hmv
    have hw0 : a' m (w : M) ≠ 0 := fun h => hm0 (by rw [h, mul_zero])
    rw [padicValRat.mul hpq hw0, padicValRat.self hp.one_lt] at hmv
    linarith
  obtain ⟨i₀, hi₀⟩ := hunit
  have hsc : IsUnit (s i₀) ∧ IsUnit (coe i₀) := by rw [hr] at hi₀; exact IsUnit.mul_iff.mp hi₀

  obtain ⟨top', htop'₀, htop'⟩ := exists_basis_update top uO i₀ hi₀
  obtain ⟨γ, hγu, hγ⟩ := exists_basis_update γ₀ uΛ i₀ hsc.1
  obtain ⟨b, hbγ, hbΛ⟩ := exists_basis_of_latticeBasis p a hbd γ
  obtain ⟨b₂, hb₂, hbO⟩ := exists_basis_of_latticeBasis p a' hbd' top'

  let e : Fin n → ℕ := fun i => if i = i₀ then 0 else (padicValRat p ((coe i : intSubring p) : ℚ)).toNat
  have hbu : b i₀ = u := by rw [hbγ, hγu]
  have hbi : ∀ i, i ≠ i₀ → b i = ((coe i : intSubring p) : ℚ) • b₂ i := by
    intro i hi
    rw [hbγ, hγ i hi, hγ₀, hb₂, htop' i hi]
  refine ⟨n, b, e, i₀, hbu, by simp [e], fun c => hbΛ c, fun c => ?_⟩

  let d : Fin n → ℚ := fun i => if i = i₀ then c i₀ else c i * ((coe i : intSubring p) : ℚ)
  have hxd : ∑ i, c i • b i = ∑ i, d i • b₂ i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i = i₀
    · subst hi
      simp only [d, if_pos rfl]
      rw [hbu, hb₂, htop'₀]
    · simp only [d, if_neg hi]
      rw [hbi i hi, smul_smul]
  have hmemO : (∀ m, 0 ≤ padicValRat p (a' m (∑ i, c i • b i))) ↔ ∀ i, d i ∈ intSubring p := by
    rw [hxd]
    exact hbO d
  rw [hmemO]
  refine forall_congr' (fun i => ?_)
  by_cases hi : i = i₀
  · subst hi
    simp only [d, e, if_pos rfl, mem_intSubring_iff, Nat.cast_zero, neg_zero]
  · simp only [d, e, if_neg hi, mem_intSubring_iff]
    have hcoeR : 0 ≤ padicValRat p ((coe i : intSubring p) : ℚ) := (coe i).2
    have hcoeQ : ((coe i : intSubring p) : ℚ) ≠ 0 := fun h => hcoe0 i (Subtype.ext h)
    rw [Int.toNat_of_nonneg hcoeR]
    by_cases hci : c i = 0
    · rw [hci, zero_mul, padicValRat.zero]
      constructor <;> intro <;> linarith
    · rw [padicValRat.mul hci hcoeQ]
      constructor <;> intro <;> linarith

end PadicLattice
p2m_reactivate "P2MW.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair.PadicLattice"

set_option maxHeartbeats 3200000 in

theorem solution
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M] (p : ℕ) [Fact p.Prime]
    (a a' : ℤ → M →ₗ[ℚ] ℚ) (hinj' : ∀ x, (∀ m, a' m x = 0) → x = 0)
    (hbd : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x))
    (hbd' : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a' m x))
    (hsub : ∀ x, (∀ m, 0 ≤ padicValRat p (a m x)) → ∀ m, 0 ≤ padicValRat p (a' m x))
    (u : M) (hu : ∀ m, 0 ≤ padicValRat p (a m u))
    (hprim : ∃ m, a' m u ≠ 0 ∧ padicValRat p (a' m u) = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ M) (e : Fin n → ℕ) (i₀ : Fin n), b i₀ = u ∧ e i₀ = 0 ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a m (∑ i, c i • b i))) ↔ ∀ i, 0 ≤ padicValRat p (c i)) ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a' m (∑ i, c i • b i))) ↔
        ∀ i, -(e i : ℤ) ≤ padicValRat p (c i)) :=
  PadicLattice.exists_basis_pair p a a' hinj' hbd hbd' hsub u hu hprim

end S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair
end P2MW
export P2MW.S_Module_exists_basis_padicValRat_apply_nonneg_iff_pair (solution)
