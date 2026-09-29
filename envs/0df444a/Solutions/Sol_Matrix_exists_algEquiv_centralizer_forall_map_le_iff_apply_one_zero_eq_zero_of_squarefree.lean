-- Prove2me | solution 1 for Matrix.exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3b4673c9-e2aa-52db-8078-a879edd7841e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree

set_option autoImplicit false

namespace BorelStab

open Matrix

variable {N : ℕ} [NeZero N]

section Morita

variable (α : (Matrix (Fin 2) (Fin 2) (ZMod N)) →+* Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) (v₀ : (Fin 2 → Fin 2 → ZMod N)) (hv₀ : ∀ w : (Fin 2 → Fin 2 → ZMod N), ∃! a : (Matrix (Fin 2) (Fin 2) (ZMod N)), w = α a v₀)

theorem α_smul (r : (ZMod N)) (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : α (r • a) = r • α a := by
  rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

def eps : (Matrix (Fin 2) (Fin 2) (ZMod N)) →ₗ[(ZMod N)] (Fin 2 → Fin 2 → ZMod N) where
  toFun a := α a v₀
  map_add' a b := by simp [map_add]
  map_smul' r a := by rw [α_smul]; rfl

@[scoped simp] theorem eps_apply (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : eps α v₀ a = α a v₀ := rfl

include hv₀ in
theorem eps_bijective : Function.Bijective (eps α v₀) := by
  refine ⟨fun a b h => ?_, fun w => ?_⟩
  · obtain ⟨c, hc, huniq⟩ := hv₀ (α a v₀)
    exact (huniq a rfl).trans (huniq b (show α a v₀ = α b v₀ from h)).symm
  · obtain ⟨a, ha, -⟩ := hv₀ w
    exact ⟨a, ha.symm⟩

noncomputable def epsE : (Matrix (Fin 2) (Fin 2) (ZMod N)) ≃ₗ[(ZMod N)] (Fin 2 → Fin 2 → ZMod N) := LinearEquiv.ofBijective (eps α v₀) (eps_bijective α v₀ hv₀)

@[scoped simp] theorem epsE_apply (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : epsE α v₀ hv₀ a = α a v₀ := rfl

theorem epsE_mul (b a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : epsE α v₀ hv₀ (b * a) = α b (epsE α v₀ hv₀ a) := by
  simp [map_mul]

theorem epsE_one : epsE α v₀ hv₀ 1 = v₀ := by simp

noncomputable def cOf (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) : (Matrix (Fin 2) (Fin 2) (ZMod N)) := (epsE α v₀ hv₀).symm (β v₀)

theorem epsE_cOf (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) : epsE α v₀ hv₀ (cOf α v₀ hv₀ β) = β v₀ := by
  simp [cOf]

theorem comm_apply_epsE (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) (hβ : β ∈ Subalgebra.centralizer (ZMod N) (Set.range α)) (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) :
    β (epsE α v₀ hv₀ a) = epsE α v₀ hv₀ (a * cOf α v₀ hv₀ β) := by
  have hcomm : α a * β = β * α a := (Subalgebra.mem_centralizer_iff (ZMod N)).mp hβ _ ⟨a, rfl⟩
  rw [epsE_mul, epsE_cOf, epsE_apply, ← epsE_one α v₀ hv₀]
  show (β * α a) (epsE α v₀ hv₀ 1) = (α a * β) (epsE α v₀ hv₀ 1)
  rw [hcomm]

theorem cOf_mul (β₁ β₂ : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) (h₁ : β₁ ∈ Subalgebra.centralizer (ZMod N) (Set.range α))
    (h₂ : β₂ ∈ Subalgebra.centralizer (ZMod N) (Set.range α)) :
    cOf α v₀ hv₀ (β₁ * β₂) = cOf α v₀ hv₀ β₂ * cOf α v₀ hv₀ β₁ := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, Module.End.mul_apply, ← epsE_cOf α v₀ hv₀ β₂, comm_apply_epsE α v₀ hv₀ β₁ h₁]

theorem cOf_one : cOf α v₀ hv₀ 1 = 1 := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, epsE_one]; rfl

theorem cOf_add (β₁ β₂ : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) :
    cOf α v₀ hv₀ (β₁ + β₂) = cOf α v₀ hv₀ β₁ + cOf α v₀ hv₀ β₂ := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, map_add, epsE_cOf, epsE_cOf]; rfl

theorem cOf_smul (r : (ZMod N)) (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) :
    cOf α v₀ hv₀ (r • β) = r • cOf α v₀ hv₀ β := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, map_smul, epsE_cOf]; rfl

noncomputable def βOf (c : (Matrix (Fin 2) (Fin 2) (ZMod N))) : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N) :=
  (epsE α v₀ hv₀).toLinearMap ∘ₗ (LinearMap.mulRight (ZMod N) c) ∘ₗ (epsE α v₀ hv₀).symm.toLinearMap

theorem βOf_mem (c : (Matrix (Fin 2) (Fin 2) (ZMod N))) : βOf α v₀ hv₀ c ∈ Subalgebra.centralizer (ZMod N) (Set.range α) := by
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  apply LinearMap.ext; intro w
  obtain ⟨a, rfl⟩ := (epsE α v₀ hv₀).surjective w
  show α b (βOf α v₀ hv₀ c (epsE α v₀ hv₀ a)) = βOf α v₀ hv₀ c (α b (epsE α v₀ hv₀ a))
  simp only [βOf, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    LinearMap.mulRight_apply, ← epsE_mul, LinearEquiv.symm_apply_apply, mul_assoc]

theorem cOf_βOf (c : (Matrix (Fin 2) (Fin 2) (ZMod N))) : cOf α v₀ hv₀ (βOf α v₀ hv₀ c) = c := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf]
  have h1 : (epsE α v₀ hv₀).symm v₀ = 1 := by rw [LinearEquiv.symm_apply_eq, epsE_one]
  show epsE α v₀ hv₀ (LinearMap.mulRight (ZMod N) c ((epsE α v₀ hv₀).symm v₀)) = epsE α v₀ hv₀ c
  rw [h1, LinearMap.mulRight_apply, one_mul]

theorem cOf_injective (β₁ β₂ : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) (h₁ : β₁ ∈ Subalgebra.centralizer (ZMod N) (Set.range α))
    (h₂ : β₂ ∈ Subalgebra.centralizer (ZMod N) (Set.range α)) (h : cOf α v₀ hv₀ β₁ = cOf α v₀ hv₀ β₂) :
    β₁ = β₂ := by
  apply LinearMap.ext; intro w
  obtain ⟨a, rfl⟩ := (epsE α v₀ hv₀).surjective w
  rw [comm_apply_epsE α v₀ hv₀ β₁ h₁, comm_apply_epsE α v₀ hv₀ β₂ h₂, h]

end Morita

end BorelStab
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

namespace BorelStab

open Matrix

variable {N : ℕ} [NeZero N]

section Rows

def rowEmb (k : Fin 2) (r : Fin 2 → ZMod N) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  fun i j => if i = k then r j else 0

def rowEmbLin (k : Fin 2) : (Fin 2 → ZMod N) →ₗ[ZMod N] Matrix (Fin 2) (Fin 2) (ZMod N) where
  toFun := rowEmb k
  map_add' r s := by ext i j; simp only [rowEmb, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c r := by ext i j; simp only [rowEmb, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

@[scoped simp] theorem rowEmbLin_apply (k : Fin 2) (r : Fin 2 → ZMod N) : rowEmbLin k r = rowEmb k r := rfl

@[scoped simp] theorem rowEmb_apply_same (k : Fin 2) (r : Fin 2 → ZMod N) : rowEmb k r k = r := by
  ext j; simp [rowEmb]

theorem rowEmb_apply_ne {k i : Fin 2} (h : i ≠ k) (r : Fin 2 → ZMod N) : rowEmb k r i = 0 := by
  ext j; simp [rowEmb, h]

theorem add_row (x y : Matrix (Fin 2) (Fin 2) (ZMod N)) (i : Fin 2) : (x + y) i = x i + y i := rfl

theorem eq_rowEmb_add (x : Matrix (Fin 2) (Fin 2) (ZMod N)) : x = rowEmb 0 (x 0) + rowEmb 1 (x 1) := by
  ext i j; fin_cases i <;> simp [rowEmb]

theorem single_mul_eq_rowEmb (k i : Fin 2) (x : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    rowEmb k (Pi.single i 1) * x = rowEmb k (x i) := by
  ext a j
  fin_cases a <;> fin_cases k <;> fin_cases i <;> simp [rowEmb, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_row (x c : Matrix (Fin 2) (Fin 2) (ZMod N)) (i : Fin 2) : (x * c) i = x i ᵥ* c := by
  ext j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem rowEmb_mul (k : Fin 2) (r : Fin 2 → ZMod N) (c : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    rowEmb k r * c = rowEmb k (r ᵥ* c) := by
  ext i j
  rw [mul_row]
  by_cases h : i = k
  · subst h; rw [rowEmb_apply_same, rowEmb_apply_same]
  · rw [rowEmb_apply_ne h, rowEmb_apply_ne h, Matrix.zero_vecMul]

theorem vecMul_two (x : Fin 2 → ZMod N) (P : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    x ᵥ* P = x 0 • P 0 + x 1 • P 1 := by
  ext j; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem single_vecMul (k : Fin 2) (P : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    (Pi.single k 1 : Fin 2 → ZMod N) ᵥ* P = P k := by
  rw [vecMul_two]; fin_cases k <;> simp

end Rows
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

section LeftIdeal

variable (J : Submodule (ZMod N) (Matrix (Fin 2) (Fin 2) (ZMod N)))
  (hJ : ∀ (b x : Matrix (Fin 2) (Fin 2) (ZMod N)), x ∈ J → b * x ∈ J)

def rowMod : Submodule (ZMod N) (Fin 2 → ZMod N) := J.comap (rowEmbLin 0)

theorem mem_rowMod (r : Fin 2 → ZMod N) : r ∈ rowMod J ↔ rowEmb 0 r ∈ J := Iff.rfl

include hJ in
theorem mem_iff_rows (x : Matrix (Fin 2) (Fin 2) (ZMod N)) : x ∈ J ↔ x 0 ∈ rowMod J ∧ x 1 ∈ rowMod J := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩ <;> rw [mem_rowMod, ← single_mul_eq_rowEmb] <;> exact hJ _ _ hx
  · rintro ⟨h0, h1⟩
    rw [eq_rowEmb_add x]
    refine J.add_mem h0 ?_
    rw [← rowEmb_apply_same 0 (x 1), ← single_mul_eq_rowEmb 1 0 (rowEmb 0 (x 1))]
    exact hJ _ _ h1

include hJ in

def rowsEquiv : ↥J ≃ ↥(rowMod J) × ↥(rowMod J) where
  toFun x := (⟨x.1 0, ((mem_iff_rows J hJ x.1).mp x.2).1⟩, ⟨x.1 1, ((mem_iff_rows J hJ x.1).mp x.2).2⟩)
  invFun p := ⟨rowEmb 0 p.1.1 + rowEmb 1 p.2.1,
    (mem_iff_rows J hJ _).mpr (by
      constructor
      · rw [add_row, rowEmb_apply_same, rowEmb_apply_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero]
        exact p.1.2
      · rw [add_row, rowEmb_apply_same, rowEmb_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]
        exact p.2.2)⟩
  left_inv x := by
    apply Subtype.ext
    exact (eq_rowEmb_add x.1).symm
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      show (rowEmb 0 p.1.1 + rowEmb 1 p.2.1) 0 = p.1.1
      rw [add_row, rowEmb_apply_same, rowEmb_apply_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero]
    · apply Subtype.ext
      show (rowEmb 0 p.1.1 + rowEmb 1 p.2.1) 1 = p.2.1
      rw [add_row, rowEmb_apply_same, rowEmb_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]

include hJ in
theorem card_eq_sq : Nat.card ↥J = Nat.card ↥(rowMod J) ^ 2 := by
  rw [Nat.card_congr (rowsEquiv J hJ), Nat.card_prod, pow_two]

include hJ in

theorem forall_mul_mem_iff (c : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    (∀ x ∈ J, x * c ∈ J) ↔ ∀ r ∈ rowMod J, r ᵥ* c ∈ rowMod J := by
  constructor
  · intro h r hr
    rw [mem_rowMod, ← rowEmb_mul]; exact h _ hr
  · intro h x hx
    rw [mem_iff_rows J hJ] at hx ⊢
    rw [mul_row, mul_row]
    exact ⟨h _ hx.1, h _ hx.2⟩

end LeftIdeal
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

section Cyclic

theorem isAddCyclic_of_card_eq (hN : Squarefree N) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M]
    (hM : Nat.card M = N) : IsAddCyclic M := by
  apply IsAddCyclic.of_exponent_eq_card
  rw [hM]
  apply Nat.dvd_antisymm
  · apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
    intro g
    rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]
  · rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hk
    match k with
    | 0 => simp
    | 1 =>
      rw [pow_one] at hk ⊢
      haveI := Fact.mk hp
      rw [← hM] at hk
      obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := M) p hk
      rw [← hg]; exact AddMonoid.addOrder_dvd_exponent g
    | k + 2 =>
      exfalso
      have : p * p ∣ N := dvd_trans ⟨p ^ k, by ring⟩ hk
      exact hp.prime.not_unit (hN p this)

end Cyclic
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

end BorelStab
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

namespace BorelStab

open Matrix

variable {N : ℕ} [NeZero N]

section Basis

theorem exists_basis (hN : Squarefree N) (L : Submodule (ZMod N) (Fin 2 → ZMod N)) (hL : Nat.card ↥L = N) :
    ∃ (u v : Fin 2 → ZMod N) (P Q : Matrix (Fin 2) (Fin 2) (ZMod N)),
      P 0 = u ∧ P 1 = v ∧ P * Q = 1 ∧ Q * P = 1 ∧ L = Submodule.span (ZMod N) {u} := by
  classical
  have hcyc := isAddCyclic_of_card_eq hN ↥L hL
  obtain ⟨u₀, hu₀⟩ := hcyc.exists_generator
  have hLu : L = Submodule.span (ZMod N) {(u₀ : Fin 2 → ZMod N)} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hu₀ ⟨x, hx⟩)
      rw [Submodule.mem_span_singleton]
      refine ⟨(n : ZMod N), ?_⟩
      have := congrArg Subtype.val hn
      rw [Int.cast_smul_eq_zsmul]
      simpa using this
    · rw [Submodule.span_singleton_le_iff_mem]; exact u₀.2
  have hcardV : Nat.card (Fin 2 → ZMod N) = N * N := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi, Fin.prod_univ_two, ZMod.card]
  have hQ : Nat.card ((Fin 2 → ZMod N) ⧸ L) = N := by
    have := Submodule.card_eq_card_quotient_mul_card L
    rw [hcardV, hL] at this
    exact (Nat.eq_of_mul_eq_mul_left (NeZero.pos N) this).symm
  obtain ⟨vb, hvb⟩ := (isAddCyclic_of_card_eq hN ((Fin 2 → ZMod N) ⧸ L) hQ).exists_generator
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective L vb
  let P : Matrix (Fin 2) (Fin 2) (ZMod N) := ![(u₀ : Fin 2 → ZMod N), v]
  have hP0 : P 0 = (u₀ : Fin 2 → ZMod N) := rfl
  have hP1 : P 1 = v := rfl
  have hsurj : Function.Surjective P.vecMul := by
    intro w
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hvb (Submodule.Quotient.mk w))
    have hmem : w - (n : ZMod N) • v ∈ L := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul, hv, Int.cast_smul_eq_zsmul, hn]
    rw [hLu, Submodule.mem_span_singleton] at hmem
    obtain ⟨s, hs⟩ := hmem
    refine ⟨![s, (n : ZMod N)], ?_⟩
    show ![s, (n : ZMod N)] ᵥ* P = w
    rw [vecMul_two, hP0, hP1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hs, sub_add_cancel]
  obtain ⟨Pu, hPu⟩ := Matrix.vecMul_surjective_iff_isUnit.mp hsurj
  refine ⟨u₀, v, P, ((Pu⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod N))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod N)),
    hP0, hP1, ?_, ?_, hLu⟩
  · rw [← hPu, Units.mul_inv]
  · rw [← hPu, Units.inv_mul]

theorem vecMul_mem_span_iff (u v : Fin 2 → ZMod N) (P Q : Matrix (Fin 2) (Fin 2) (ZMod N))
    (hP0 : P 0 = u) (hP1 : P 1 = v) (hPQ : P * Q = 1) (hQP : Q * P = 1) (c : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    u ᵥ* c ∈ Submodule.span (ZMod N) {u} ↔ (P * c * Q) 0 1 = 0 := by
  set M := P * c * Q with hM
  have key : u ᵥ* c = M 0 0 • u + M 0 1 • v := by
    have h1 : u ᵥ* c = (M 0) ᵥ* P := by
      rw [← hP0, ← single_vecMul 0 P, Matrix.vecMul_vecMul, ← single_vecMul 0 M, Matrix.vecMul_vecMul, hM,
        Matrix.mul_assoc, Matrix.mul_assoc, hQP, Matrix.mul_one]
    rw [h1, vecMul_two, hP0, hP1]
  rw [key, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, hs⟩
    have h0 : ![M 0 0 - s, M 0 1] ᵥ* P = 0 := by
      rw [vecMul_two, hP0, hP1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_smul]
      rw [hs]; abel
    have : ![M 0 0 - s, M 0 1] = 0 := by
      have := congrArg (fun x => x ᵥ* Q) h0
      simpa only [Matrix.vecMul_vecMul, hPQ, Matrix.vecMul_one, Matrix.zero_vecMul] using this
    have := congrFun this 1
    simpa using this
  · intro h; exact ⟨M 0 0, by rw [h, zero_smul, add_zero]⟩

end Basis
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

section Assembly

variable (α : (Matrix (Fin 2) (Fin 2) (ZMod N)) →+* Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))
  (v₀ : (Fin 2 → Fin 2 → ZMod N)) (hv₀ : ∀ w : (Fin 2 → Fin 2 → ZMod N), ∃! a : (Matrix (Fin 2) (Fin 2) (ZMod N)), w = α a v₀)

theorem cOf_zero : cOf α v₀ hv₀ 0 = 0 := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, map_zero]; rfl

noncomputable def thetaHom (P Q : Matrix (Fin 2) (Fin 2) (ZMod N)) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ↥(Subalgebra.centralizer (ZMod N) (Set.range α)) →ₐ[ZMod N] Matrix (Fin 2) (Fin 2) (ZMod N) where
  toFun β := (P * cOf α v₀ hv₀ β.1 * Q)ᵀ
  map_one' := by
    show (P * cOf α v₀ hv₀ 1 * Q)ᵀ = 1
    rw [cOf_one, Matrix.mul_one, hPQ, Matrix.transpose_one]
  map_mul' β₁ β₂ := by
    show (P * cOf α v₀ hv₀ (β₁.1 * β₂.1) * Q)ᵀ = (P * cOf α v₀ hv₀ β₁.1 * Q)ᵀ * (P * cOf α v₀ hv₀ β₂.1 * Q)ᵀ
    rw [cOf_mul α v₀ hv₀ _ _ β₁.2 β₂.2, ← Matrix.transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  map_zero' := by
    show (P * cOf α v₀ hv₀ 0 * Q)ᵀ = 0
    rw [cOf_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.transpose_zero]
  map_add' β₁ β₂ := by
    show (P * cOf α v₀ hv₀ (β₁.1 + β₂.1) * Q)ᵀ = (P * cOf α v₀ hv₀ β₁.1 * Q)ᵀ + (P * cOf α v₀ hv₀ β₂.1 * Q)ᵀ
    rw [cOf_add, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add]
  commutes' r := by
    show (P * cOf α v₀ hv₀ (algebraMap (ZMod N) _ r) * Q)ᵀ = algebraMap (ZMod N) _ r
    rw [Algebra.algebraMap_eq_smul_one, cOf_smul, cOf_one, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hPQ, Matrix.transpose_smul, Matrix.transpose_one]

theorem thetaHom_apply (P Q : Matrix (Fin 2) (Fin 2) (ZMod N)) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (β : ↥(Subalgebra.centralizer (ZMod N) (Set.range α))) :
    thetaHom α v₀ hv₀ P Q hPQ hQP β = (P * cOf α v₀ hv₀ β.1 * Q)ᵀ := rfl

theorem thetaHom_bijective (P Q : Matrix (Fin 2) (Fin 2) (ZMod N)) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Function.Bijective (thetaHom α v₀ hv₀ P Q hPQ hQP) := by
  constructor
  · intro β₁ β₂ h
    rw [thetaHom_apply, thetaHom_apply] at h
    have h0 : P * cOf α v₀ hv₀ β₁.1 * Q = P * cOf α v₀ hv₀ β₂.1 * Q := by
      have := congrArg Matrix.transpose h
      simpa only [Matrix.transpose_transpose] using this
    have e : ∀ c : Matrix (Fin 2) (Fin 2) (ZMod N), c = Q * (P * c * Q) * P := fun c => by
      calc c = (Q * P) * c * (Q * P) := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
        _ = Q * (P * c * Q) * P := by simp only [Matrix.mul_assoc]
    have h' : cOf α v₀ hv₀ β₁.1 = cOf α v₀ hv₀ β₂.1 := by
      rw [e (cOf α v₀ hv₀ β₁.1), h0, ← e]
    exact Subtype.ext (cOf_injective α v₀ hv₀ _ _ β₁.2 β₂.2 h')
  · intro m
    refine ⟨⟨βOf α v₀ hv₀ (Q * mᵀ * P), βOf_mem α v₀ hv₀ _⟩, ?_⟩
    rw [thetaHom_apply]
    show (P * cOf α v₀ hv₀ (βOf α v₀ hv₀ (Q * mᵀ * P)) * Q)ᵀ = m
    rw [cOf_βOf]
    simp only [Matrix.mul_assoc]
    rw [hPQ, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.transpose_transpose]

end Assembly
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

end BorelStab
p2m_reactivate "P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.BorelStab"

open BorelStab in
theorem solution
    (N : ℕ) [NeZero N] (hN : Squarefree N)
    (α : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))
    (hfree : ∃ v₀ : Fin 2 → Fin 2 → ZMod N, ∀ w : Fin 2 → Fin 2 → ZMod N,
      ∃! a : Matrix (Fin 2) (Fin 2) (ZMod N), w = α a v₀)
    (W : Submodule (ZMod N) (Fin 2 → Fin 2 → ZMod N))
    (hWstab : ∀ (a : Matrix (Fin 2) (Fin 2) (ZMod N)) (w : Fin 2 → Fin 2 → ZMod N), w ∈ W → α a w ∈ W)
    (hWcard : Nat.card ↥W = N ^ 2) :
    ∃ θ : ↥(Subalgebra.centralizer (ZMod N) (Set.range α)) ≃ₐ[ZMod N] Matrix (Fin 2) (Fin 2) (ZMod N),
      ∀ (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))
        (hβ : β ∈ Subalgebra.centralizer (ZMod N) (Set.range α)),
        Submodule.map β W ≤ W ↔ θ ⟨β, hβ⟩ 1 0 = 0 := by
  classical
  obtain ⟨v₀, hv₀⟩ := hfree

  let J : Submodule (ZMod N) (Matrix (Fin 2) (Fin 2) (ZMod N)) := W.comap (epsE α v₀ hv₀).toLinearMap
  have hJmem : ∀ x, x ∈ J ↔ epsE α v₀ hv₀ x ∈ W := fun x => Iff.rfl
  have hJ : ∀ (b x : Matrix (Fin 2) (Fin 2) (ZMod N)), x ∈ J → b * x ∈ J := by
    intro b x hx
    rw [hJmem, epsE_mul]
    exact hWstab b _ ((hJmem x).mp hx)
  have hJcard : Nat.card ↥J = N ^ 2 := by
    rw [← hWcard]
    have hmap : J.map (epsE α v₀ hv₀).toLinearMap = W :=
      Submodule.map_comap_eq_of_surjective (epsE α v₀ hv₀).surjective W
    exact Nat.card_congr (LinearEquiv.ofSubmodules (epsE α v₀ hv₀) J W hmap).toEquiv
  have hLcard : Nat.card ↥(rowMod J) = N := by
    have := card_eq_sq J hJ
    rw [hJcard] at this
    exact (Nat.pow_left_injective two_ne_zero this).symm
  obtain ⟨u, v, P, Q, hP0, hP1, hPQ, hQP, hLu⟩ := exists_basis hN (rowMod J) hLcard
  refine ⟨AlgEquiv.ofBijective (thetaHom α v₀ hv₀ P Q hPQ hQP) (thetaHom_bijective α v₀ hv₀ P Q hPQ hQP),
    fun β hβ => ?_⟩
  rw [AlgEquiv.ofBijective_apply, thetaHom_apply, Matrix.transpose_apply]
  rw [← vecMul_mem_span_iff u v P Q hP0 hP1 hPQ hQP]

  have step1 : Submodule.map β W ≤ W ↔ ∀ x ∈ J, x * cOf α v₀ hv₀ β ∈ J := by
    rw [Submodule.map_le_iff_le_comap]
    constructor
    · intro h x hx
      rw [hJmem, ← comm_apply_epsE α v₀ hv₀ β hβ]
      exact h ((hJmem x).mp hx)
    · intro h w hw
      obtain ⟨x, rfl⟩ := (epsE α v₀ hv₀).surjective w
      show β (epsE α v₀ hv₀ x) ∈ W
      rw [comm_apply_epsE α v₀ hv₀ β hβ, ← hJmem]
      exact h x ((hJmem x).mpr hw)
  rw [step1, forall_mul_mem_iff J hJ, hLu]
  constructor
  · intro h; exact h u (Submodule.mem_span_singleton_self u)
  · intro h r hr
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hr
    rw [Matrix.smul_vecMul]
    exact Submodule.smul_mem _ s h

end S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree
end P2MW
export P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree (solution)
