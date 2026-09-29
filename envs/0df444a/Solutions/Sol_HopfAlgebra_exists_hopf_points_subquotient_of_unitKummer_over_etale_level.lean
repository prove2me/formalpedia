-- Prove2me | solution 1 for HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3671b4c8-2a7e-5ef9-af63-ebc646ba40b1

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_KummerRadicands
import Theorems.Thm_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer
import Theorems.Thm_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup
import Theorems.Thm_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopf_points_subquotient_of_unitKummer_over_etale_level

set_option autoImplicit false

set_option maxHeartbeats 1600000

namespace S17Pkg

open scoped TensorProduct
open WithConv HopfAlgebra.KummerRadicands

variable {O : Type} [CommRing O] {n : ℕ} [NeZero n] {a : ℕ} (rr : Fin a → Oˣ)
variable {L : Type} [Field L] [Algebra O L] (ρ : Fin a → L) (hρ : ∀ k, ρ k ^ n = algebraMap O L (rr k : O))

noncomputable def rootFam (l : Fin a → ZMod n) : L := ∏ k, ρ k ^ (l k).val

omit [NeZero n] in
theorem rootFam_zero : rootFam ρ (0 : Fin a → ZMod n) = 1 := by
  simp [rootFam]

include hρ in
theorem rootFam_pow (l : Fin a → ZMod n) : rootFam ρ l ^ n = algebraMap O L (rad rr l : O) := by
  simp only [rootFam, rad, Units.coe_prod, Units.val_pow_eq_pow_val, map_prod, map_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, hρ]

include hρ in

theorem rootFam_add (l l' : Fin a → ZMod n) :
    rootFam ρ (l + l') = algebraMap O L (carry rr l l' : O) * rootFam ρ l * rootFam ρ l' := by
  simp only [rootFam, carry, Units.coe_prod, map_prod, ← Finset.prod_mul_distrib, Pi.add_apply]
  refine Finset.prod_congr rfl fun k _ => ?_

  set v := (l k).val
  set v' := (l' k).val
  have hvv : (l k + l' k).val = (v + v') % n := ZMod.val_add _ _
  have hunit : algebraMap O L ((rr k)⁻¹ : Oˣ) * algebraMap O L (rr k : O) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hvv, Units.val_pow_eq_pow_val, map_pow]
  have key : ρ k ^ (v + v') = ρ k ^ ((v + v') % n) * (algebraMap O L (rr k : O)) ^ ((v + v') / n) := by
    conv_lhs => rw [← Nat.mod_add_div (v + v') n, pow_add, pow_mul, hρ]
  have hne : algebraMap O L (rr k : O) ^ ((v + v') / n) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    rw [h0, mul_zero] at hunit
    exact zero_ne_one hunit
  apply mul_right_cancel₀ hne
  rw [mul_assoc, mul_assoc]
  calc ρ k ^ ((v + v') % n) * algebraMap O L (rr k : O) ^ ((v + v') / n) = ρ k ^ (v + v') := key.symm
    _ = (algebraMap O L ((rr k)⁻¹ : Oˣ) * algebraMap O L (rr k : O)) ^ ((v + v') / n) * (ρ k ^ v * ρ k ^ v') := by
        rw [hunit, one_pow, one_mul, pow_add]
    _ = algebraMap O L (((rr k)⁻¹ : Oˣ) : O) ^ ((v + v') / n) * (ρ k ^ v * (ρ k ^ v' * algebraMap O L (rr k : O) ^ ((v + v') / n))) := by
        rw [mul_pow]; ring

theorem rootFam_gal (ζ : L) (hζn : ζ ^ n = 1) (τ : L →ₐ[O] L) (κ : Fin a → ℕ) (hτ : ∀ k, τ (ρ k) = ζ ^ κ k * ρ k)
    (l : Fin a → ZMod n) :
    τ (rootFam ρ l) = ζ ^ (∑ k, κ k * (l k).val) * rootFam ρ l := by
  simp only [rootFam, map_prod, map_pow, hτ, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]

theorem natCast_sum_exponent (κ : Fin a → ℕ) (l : Fin a → ZMod n) :
    ((∑ k, κ k * (l k).val : ℕ) : ZMod n) = ∑ k, κ k • l k := by
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ZMod.natCast_val, ZMod.cast_id', id, nsmul_eq_mul]

end S17Pkg

namespace S17Pkg

open scoped TensorProduct
open WithConv

variable {R : Type} [CommRing R] (A B : Type) [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  (L : Type) [CommRing L] [Algebra R L]

noncomputable def tens (fg : WithConv (A →ₐ[R] L) × WithConv (B →ₐ[R] L)) : WithConv (A ⊗[R] B →ₐ[R] L) :=
  toConv (Algebra.TensorProduct.lift fg.1.ofConv fg.2.ofConv (fun _ _ => Commute.all _ _))

theorem tens_tmul (fg : WithConv (A →ₐ[R] L) × WithConv (B →ₐ[R] L)) (x : A) (y : B) :
    (tens A B L fg).ofConv (x ⊗ₜ y) = fg.1.ofConv x * fg.2.ofConv y :=
  Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) x y

noncomputable def tensEquiv : (WithConv (A →ₐ[R] L) × WithConv (B →ₐ[R] L)) ≃ WithConv (A ⊗[R] B →ₐ[R] L) where
  toFun := tens A B L
  invFun F := (toConv (F.ofConv.comp (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)),
    toConv (F.ofConv.comp (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)))
  left_inv fg := by
    apply Prod.ext
    · apply WithConv.ext; apply AlgHom.ext; intro x
      show (tens A B L fg).ofConv (x ⊗ₜ 1) = fg.1.ofConv x
      rw [tens_tmul, map_one, mul_one]
    · apply WithConv.ext; apply AlgHom.ext; intro y
      show (tens A B L fg).ofConv (1 ⊗ₜ y) = fg.2.ofConv y
      rw [tens_tmul, map_one, one_mul]
  right_inv F := by
    apply WithConv.ext
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [tens_tmul]
    show F.ofConv (x ⊗ₜ 1) * F.ofConv (1 ⊗ₜ y) = F.ofConv (x ⊗ₜ y)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem tensEquiv_apply (fg : WithConv (A →ₐ[R] L) × WithConv (B →ₐ[R] L)) : tensEquiv A B L fg = tens A B L fg := rfl

theorem tens_mul (fg fg' : WithConv (A →ₐ[R] L) × WithConv (B →ₐ[R] L)) :
    tens A B L (fg * fg') = tens A B L fg * tens A B L fg' := by
  classical
  obtain ⟨f, g⟩ := fg
  obtain ⟨f', g'⟩ := fg'
  apply WithConv.ext
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [tens_tmul]
  show (f * f').ofConv x * (g * g').ofConv y = ((tens A B L (f, g)) * (tens A B L (f', g'))).ofConv (x ⊗ₜ y)
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul]
  let 𝓡 := Coalgebra.Repr.arbitrary R x
  let 𝓢 := Coalgebra.Repr.arbitrary R y
  conv_lhs => rw [← 𝓡.eq, ← 𝓢.eq]
  conv_rhs => rw [← 𝓡.eq, ← 𝓢.eq]
  simp only [map_sum, TensorProduct.sum_tmul, TensorProduct.tmul_sum, Algebra.TensorProduct.lift_tmul,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, ofConv_toConv]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [tens_tmul, tens_tmul]
  ring

end S17Pkg

namespace S17Pkg

open scoped TensorProduct
open WithConv HopfAlgebra.KummerRadicands

theorem core_one (O : Type) [CommRing O] [Nontrivial O] (p N : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra O L] (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (a : ℕ) (rr : Fin a → Oˣ) (ρ : Fin a → L) (hρ : ∀ k, ρ k ^ (p ^ N) = algebraMap O L (rr k : O)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra O H),
      Module.Finite O H ∧ Module.Free O H ∧ Coalgebra.IsCocomm O H ∧
      ∃ ψ : ZMod (p ^ N) × (Fin a → ZMod (p ^ N)) ≃ WithConv (H →ₐ[O] L),
        (∀ x y, ψ (x + y) = ψ x * ψ y) ∧
        ∀ (τ : L →ₐ[O] L) (e : ℕ) (κ : Fin a → ℕ), τ ζ = ζ ^ e → (∀ k, τ (ρ k) = ζ ^ κ k * ρ k) →
          ∀ (i : ZMod (p ^ N)) (l : Fin a → ZMod (p ^ N)) (h : H),
            ψ (e • i + ∑ k, κ k • l k, l) h = τ (ψ (i, l) h) := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨H, iCR, iHA, hfin, hfree, hcoc, -, hpts⟩ :=
    HopfAlgebra.exists_kummerCarrier_withConv_equiv_of_kummerCocycle O p N (Fin a → ZMod (p ^ N))
      (fun l => (rad rr l : O)) (fun l => (rad rr l).isUnit)
      (by show ((rad rr (0 : Fin a → ZMod (p ^ N)) : Oˣ) : O) = 1; rw [rad_zero]; rfl)
      (fun l l' => (carry rr l l' : O))
      (fun l l' => by
        have := congrArg Units.val (carry_pow_mul_rad_mul_rad rr l l')
        simpa [Units.val_mul, Units.val_pow_eq_pow_val] using this)
      (fun l => by show ((carry rr 0 l : Oˣ) : O) = 1; rw [carry_zero_left]; rfl)
      (fun l l' => by show ((carry rr l l' : Oˣ) : O) = (carry rr l' l : O); rw [carry_comm])
      (fun l l' l'' => by
        have := congrArg Units.val (carry_mul_carry_add rr l l' l'')
        simp only [Units.val_mul] at this
        rw [this, mul_comm])
  obtain ⟨ψ, hψmul, hψgal⟩ := hpts L ζ hζ (rootFam ρ) (rootFam_pow rr ρ hρ) (rootFam_zero ρ) (rootFam_add rr ρ hρ)
  refine ⟨H, iCR, iHA, hfin, hfree, hcoc, ψ, hψmul, ?_⟩
  intro τ e κ hτζ hτ i l h
  have := hψgal τ e (fun l => ∑ k, κ k * (l k).val) hτζ (fun l => rootFam_gal ρ ζ hζ.pow_eq_one τ κ hτ l) i l h
  rwa [natCast_sum_exponent] at this

def splitEquiv (X Y : Type) (b : ℕ) :
    ((Fin (b + 1) → X) × (Fin (b + 1) → Y)) ≃ (X × Y) × ((Fin b → X) × (Fin b → Y)) where
  toFun il := ((il.1 0, il.2 0), (Fin.tail il.1, Fin.tail il.2))
  invFun z := (Fin.cons z.1.1 z.2.1, Fin.cons z.1.2 z.2.2)
  left_inv il := by simp
  right_inv z := by simp

theorem exists_productCarrier_points
    (O : Type) [CommRing O] [Nontrivial O] (p N : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra O L] (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (b a : ℕ) (rr : Fin b → Fin a → Oˣ) (ρρ : Fin b → Fin a → L)
    (hρ : ∀ m k, ρρ m k ^ (p ^ N) = algebraMap O L (rr m k : O)) :
    ∃ (HB : Type) (_ : CommRing HB) (_ : HopfAlgebra O HB),
      Module.Finite O HB ∧ Module.Free O HB ∧ Coalgebra.IsCocomm O HB ∧
      ∃ Ψ : (Fin b → ZMod (p ^ N)) × (Fin b → Fin a → ZMod (p ^ N)) ≃ WithConv (HB →ₐ[O] L),
        (∀ x y, Ψ (x + y) = Ψ x * Ψ y) ∧
        ∀ (τ : L →ₐ[O] L) (e : ℕ) (κ : Fin b → Fin a → ℕ), τ ζ = ζ ^ e → (∀ m k, τ (ρρ m k) = ζ ^ κ m k * ρρ m k) →
          ∀ (i : Fin b → ZMod (p ^ N)) (l : Fin b → Fin a → ZMod (p ^ N)) (h : HB),
            Ψ (fun m => e • i m + ∑ k, κ m k • l m k, l) h = τ (Ψ (i, l) h) := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  induction b with
  | zero =>
    refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    let Ψ : (Fin 0 → ZMod (p ^ N)) × (Fin 0 → Fin a → ZMod (p ^ N)) ≃ WithConv (O →ₐ[O] L) :=
      { toFun := fun _ => 1
        invFun := fun _ => (Fin.elim0, Fin.elim0)
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun F => WithConv.ext (Subsingleton.elim _ _) }
    refine ⟨Ψ, fun _ _ => (mul_one _).symm, ?_⟩
    intro τ e κ _ _ i l h
    show (1 : WithConv (O →ₐ[O] L)) h = τ ((1 : WithConv (O →ₐ[O] L)) h)
    rw [AlgHom.convOne_apply, CommSemiring.counit_apply, AlgHom.commutes]
  | succ b ih =>
    obtain ⟨H₀, iCR₀, iHA₀, hfin₀, hfree₀, hcoc₀, ψ₀, hψ₀mul, hψ₀gal⟩ :=
      core_one O p N L ζ hζ a (rr 0) (ρρ 0) (hρ 0)
    obtain ⟨HB', iCR', iHA', hfin', hfree', hcoc', Ψ', hΨ'mul, hΨ'gal⟩ :=
      ih (fun m => rr m.succ) (fun m => ρρ m.succ) (fun m k => hρ m.succ k)
    haveI := hfin₀; haveI := hfree₀; haveI := hcoc₀; haveI := hfin'; haveI := hfree'; haveI := hcoc'
    refine ⟨H₀ ⊗[O] HB', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    let Ψ : (Fin (b + 1) → ZMod (p ^ N)) × (Fin (b + 1) → Fin a → ZMod (p ^ N)) ≃ WithConv (H₀ ⊗[O] HB' →ₐ[O] L) :=
      (splitEquiv _ _ b).trans ((ψ₀.prodCongr Ψ').trans (tensEquiv H₀ HB' L))
    have hΨ : ∀ il, Ψ il = tens H₀ HB' L (ψ₀ (il.1 0, il.2 0), Ψ' (Fin.tail il.1, Fin.tail il.2)) := fun _ => rfl
    refine ⟨Ψ, ?_, ?_⟩
    · intro x y
      rw [hΨ, hΨ, hΨ, ← tens_mul, Prod.mk_mul_mk, ← hψ₀mul, ← hΨ'mul]
      rfl
    · intro τ e κ hτζ hτ i l h
      have key : (Ψ (fun m => e • i m + ∑ k, κ m k • l m k, l)).ofConv =
          (τ.comp (Ψ (i, l)).ofConv) := by
        rw [hΨ, hΨ]
        apply Algebra.TensorProduct.ext'
        intro x y
        rw [tens_tmul, AlgHom.comp_apply, tens_tmul, map_mul]
        congr 1
        · exact hψ₀gal τ e (κ 0) hτζ (fun k => hτ 0 k) (i 0) (l 0) x
        · exact hΨ'gal τ e (fun m => κ m.succ) hτζ (fun m k => hτ m.succ k) (Fin.tail i) (Fin.tail l) y
      exact AlgHom.congr_fun key h

end S17Pkg

namespace S17CarrierPkg

variable (p : ℕ) [Fact p.Prime] (N : ℕ)

local notation "𝕃" => AlgebraicClosure ℚ_[p]
local notation "Γ" => (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])

def fixer (B : Type) [CommRing B] [Algebra B 𝕃] : Subgroup Γ where
  carrier := {σ | ∀ b : B, σ (algebraMap B 𝕃 b) = algebraMap B 𝕃 b}
  mul_mem' {σ τ} hσ hτ b := by rw [AlgEquiv.mul_apply, hτ, hσ]
  one_mem' b := rfl
  inv_mem' {σ} hσ b := by
    have h := hσ b
    conv_lhs => rw [← h]
    exact σ.symm_apply_apply _

theorem exists_carrier_over_level
    (hp2 : p ≠ 2) (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction Γ M]
    (n : Γ → ℕ) (hn : ∀ (τ : Γ) (ξ : 𝕃), ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)
    (ζ : 𝕃) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] [Module.Free ℤ_[p] B] [Algebra.Etale ℤ_[p] B]
    [Algebra B 𝕃] [IsScalarTower ℤ_[p] B 𝕃]
    (b a : ℕ) (w : Fin b → Fin a → Bˣ) (ρ : Fin b → Fin a → 𝕃) (κ : Γ → Fin b → Fin a → ℕ)
    (hρ : ∀ m k, ρ m k ^ p ^ N = algebraMap B 𝕃 (w m k : B))
    (hκ : ∀ σ ∈ fixer p B, ∀ m k, σ (ρ m k) = ζ ^ κ σ m k * ρ m k)
    (π : (Fin b → ZMod (p ^ N)) × (Fin a → ZMod (p ^ N)) →+ M) (hπ : Function.Surjective π)
    (hπσ : ∀ σ ∈ fixer p B, ∀ (i : Fin b → ZMod (p ^ N)) (l : Fin a → ZMod (p ^ N)),
      π (fun m => n σ • i m + ∑ k, κ σ m k • l k, l) = σ • π (i, l)) :
    ∃ (HB : Type) (_ : CommRing HB) (_ : HopfAlgebra B HB) (_ : Module.Finite B HB) (_ : Module.Free B HB)
      (_ : Coalgebra.IsCocomm B HB)
      (Q' : AddSubmonoid (Additive (WithConv (HB →ₐ[B] 𝕃))))
      (ρ' : ↥Q' →+ M),
      Function.Surjective ρ' ∧
      (∀ f : ↥Q', ∃ g : ↥Q', (f : Additive (WithConv (HB →ₐ[B] 𝕃))) + g = 0) ∧
      (∀ σ : Γ, (∀ b : B, σ (algebraMap B 𝕃 b) = algebraMap B 𝕃 b) →
        ∀ (f : ↥Q') (g : WithConv (HB →ₐ[B] 𝕃)),
          (∀ h : HB, g h = σ (Additive.toMul (f : Additive (WithConv (HB →ₐ[B] 𝕃))) h)) →
            ∃ hg : Additive.ofMul g ∈ Q', ρ' ⟨Additive.ofMul g, hg⟩ = σ • ρ' f) := by
  classical
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

  let w' : Fin (b + 1) → Fin a → Bˣ := Fin.cons (fun _ => 1) w
  let ρ'' : Fin (b + 1) → Fin a → 𝕃 := Fin.cons (fun _ => 1) ρ
  have hw'0 : ∀ k, w' 0 k = 1 := fun _ => rfl
  have hw's : ∀ m k, w' (Fin.succ m) k = w m k := fun _ _ => rfl
  have hρ''0 : ∀ k, ρ'' 0 k = 1 := fun _ => rfl
  have hρ''s : ∀ m k, ρ'' (Fin.succ m) k = ρ m k := fun _ _ => rfl
  have hρ'' : ∀ m k, ρ'' m k ^ p ^ N = algebraMap B 𝕃 (w' m k : B) := by
    intro m k
    refine Fin.cases ?_ (fun m => ?_) m
    · rw [hρ''0, hw'0, one_pow, Units.val_one, map_one]
    · rw [hρ''s, hw's]; exact hρ m k
  obtain ⟨HB, i1, i2, hfin, hfree, hcoc, Ψ, hΨadd, hΨτ⟩ :=
    S17Pkg.exists_productCarrier_points B p N 𝕃 ζ hζ (b + 1) a w' ρ'' hρ''

  let Φ : (Fin (b + 1) → ZMod (p ^ N)) × (Fin (b + 1) → Fin a → ZMod (p ^ N)) ≃+ Additive (WithConv (HB →ₐ[B] 𝕃)) :=
    { toFun := fun x => Additive.ofMul (Ψ x)
      invFun := fun f => Ψ.symm (Additive.toMul f)
      left_inv := fun x => by simp
      right_inv := fun f => by simp
      map_add' := fun x y => by
        show Additive.ofMul (Ψ (x + y)) = Additive.ofMul (Ψ x) + Additive.ofMul (Ψ y)
        rw [hΨadd]; rfl }
  have hΦ : ∀ x, Φ x = Additive.ofMul (Ψ x) := fun _ => rfl

  let P : AddSubgroup ((Fin (b + 1) → ZMod (p ^ N)) × (Fin (b + 1) → Fin a → ZMod (p ^ N))) :=
    { carrier := {x | x.1 0 = 0 ∧ ∀ m, x.2 m = x.2 0}
      add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], fun m => by simp [hx.2 m, hy.2 m]⟩
      zero_mem' := ⟨rfl, fun _ => rfl⟩
      neg_mem' := fun {x} hx => ⟨by simp [hx.1], fun m => by simp [hx.2 m]⟩ }
  have hPmem : ∀ x, x ∈ P ↔ x.1 0 = 0 ∧ ∀ m, x.2 m = x.2 0 := fun _ => Iff.rfl
  let coll : ((Fin (b + 1) → ZMod (p ^ N)) × (Fin (b + 1) → Fin a → ZMod (p ^ N))) →+
      ((Fin b → ZMod (p ^ N)) × (Fin a → ZMod (p ^ N))) :=
    { toFun := fun x => (fun m => x.1 m.succ, x.2 0)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hcoll : ∀ x, coll x = (fun m => x.1 m.succ, x.2 0) := fun _ => rfl

  let Q' : AddSubmonoid (Additive (WithConv (HB →ₐ[B] 𝕃))) := (P.toAddSubmonoid).map Φ.toAddMonoidHom
  let ρfull : Additive (WithConv (HB →ₐ[B] 𝕃)) →+ M := (π.comp coll).comp Φ.symm.toAddMonoidHom
  let ρ' : ↥Q' →+ M := ρfull.comp Q'.subtype
  have hρ'apply : ∀ (x) (hx : Φ x ∈ Q'), ρ' ⟨Φ x, hx⟩ = π (coll x) := by
    intro x hx
    show π (coll (Φ.symm (Φ x))) = _
    rw [AddEquiv.symm_apply_apply]
  have hmemQ' : ∀ f, f ∈ Q' ↔ ∃ x ∈ P, Φ x = f := by
    intro f
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  refine ⟨HB, i1, i2, hfin, hfree, hcoc, Q', ρ', ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨⟨i, l⟩, rfl⟩ := hπ y
    let x : (Fin (b + 1) → ZMod (p ^ N)) × (Fin (b + 1) → Fin a → ZMod (p ^ N)) := (Fin.cons 0 i, fun _ => l)
    have hx : x ∈ P := ⟨rfl, fun _ => rfl⟩
    refine ⟨⟨Φ x, (hmemQ' _).mpr ⟨x, hx, rfl⟩⟩, ?_⟩
    rw [hρ'apply, hcoll]
    rfl
  ·
    rintro ⟨f, hf⟩
    obtain ⟨x, hx, rfl⟩ := (hmemQ' f).mp hf
    refine ⟨⟨Φ (-x), (hmemQ' _).mpr ⟨-x, P.neg_mem hx, rfl⟩⟩, ?_⟩
    show Φ x + Φ (-x) = 0
    rw [← map_add, add_neg_cancel, map_zero]
  ·
    intro σ hσB f g hg
    obtain ⟨x, hx, hxf⟩ := (hmemQ' f).mp f.2

    let τ : 𝕃 →ₐ[B] 𝕃 := { σ.toRingEquiv.toRingHom with commutes' := hσB }
    have hτ : ∀ y, τ y = σ y := fun _ => rfl
    have hσfix : σ ∈ fixer p B := hσB
    have hτζ : τ ζ = ζ ^ n σ := hn σ ζ hζ.pow_eq_one
    let κ' : Fin (b + 1) → Fin a → ℕ := Fin.cons (fun _ => 0) (κ σ)
    have hκ'0 : ∀ k, κ' 0 k = 0 := fun _ => rfl
    have hκ's : ∀ m k, κ' (Fin.succ m) k = κ σ m k := fun _ _ => rfl
    have hτρ : ∀ m k, τ (ρ'' m k) = ζ ^ κ' m k * ρ'' m k := by
      intro m k
      refine Fin.cases ?_ (fun m => ?_) m
      · rw [hρ''0, hκ'0, map_one, pow_zero, one_mul]
      · rw [hρ''s, hκ's, hτ]; exact hκ σ hσfix m k

    let x' : (Fin (b + 1) → ZMod (p ^ N)) × (Fin (b + 1) → Fin a → ZMod (p ^ N)) :=
      (fun m => n σ • x.1 m + ∑ k, κ' m k • x.2 m k, x.2)
    have hx' : x' ∈ P := by
      refine ⟨?_, hx.2⟩
      show n σ • x.1 0 + ∑ k, κ' 0 k • x.2 0 k = 0
      rw [hx.1, smul_zero, zero_add]
      exact Finset.sum_eq_zero (fun k _ => by rw [hκ'0, zero_smul])
    have hgx' : g = Ψ x' := by
      apply WithConv.ext
      apply AlgHom.ext
      intro h
      rw [hg h]
      have hf : Additive.toMul (f : Additive (WithConv (HB →ₐ[B] 𝕃))) = Ψ x := by
        rw [← hxf, hΦ]; rfl
      rw [hf]
      have := hΨτ τ (n σ) κ' hτζ hτρ x.1 x.2 h
      rw [hτ] at this
      exact this.symm
    have hgQ : Additive.ofMul g ∈ Q' := (hmemQ' _).mpr ⟨x', hx', by rw [hΦ, hgx']⟩
    refine ⟨hgQ, ?_⟩
    have e1 : (⟨Additive.ofMul g, hgQ⟩ : ↥Q') = ⟨Φ x', (hmemQ' _).mpr ⟨x', hx', rfl⟩⟩ := by
      apply Subtype.ext
      show Additive.ofMul g = Φ x'
      rw [hΦ, hgx']
    have e2 : f = ⟨Φ x, (hmemQ' _).mpr ⟨x, hx, rfl⟩⟩ := Subtype.ext hxf.symm
    rw [e1, e2, hρ'apply, hρ'apply, hcoll, hcoll]

    have key := hπσ σ hσfix (fun m => x.1 m.succ) (x.2 0)
    rw [← key]
    congr 1
    ext m
    · show n σ • x.1 m.succ + ∑ k, κ' m.succ k • x.2 m.succ k = _
      rw [hx.2 (Fin.succ m)]
      rfl
    · rfl

end S17CarrierPkg

open S17CarrierPkg in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ)
    (M : Type) [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (hM : ∀ x : M, IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x : Set (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])))
    (hpM : ∀ x : M, (p ^ N) • x = 0)
    (M₁ : AddSubgroup M) (hM₁ : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])), ∀ y ∈ M₁, σ • y ∈ M₁)
    (n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ)
    (hn : ∀ (τ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (ξ : AlgebraicClosure ℚ_[p]), ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)
    (hmult : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ y ∈ M₁, τ • y = n τ • y)
    (hquot : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ x : M, τ • x - x ∈ M₁)
    (ζ : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ_[p])
    (hu : ∀ i, (padicIntegers p).valuation (u i) = 1)
    (huI : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (φ : Fin t → (M →+ M)) (hφ₁ : ∀ i x, φ i x ∈ M₁) (hφ₀ : ∀ i, ∀ y ∈ M₁, φ i y = 0)
    (hdec : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], (∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → ∀ x : M, τ • x - x = ∑ i, (k i) • φ i x) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B)
      (_ : Module.Free ℤ_[p] B) (_ : Algebra.Etale ℤ_[p] B)
      (_ : Algebra B (AlgebraicClosure ℚ_[p])) (_ : IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p]))
      (HB : Type) (_ : CommRing HB) (_ : HopfAlgebra B HB) (_ : Module.Finite B HB) (_ : Module.Free B HB)
      (_ : Coalgebra.IsCocomm B HB)
      (Q' : AddSubmonoid (Additive (WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p]))))
      (ρ : ↥Q' →+ M),
      Function.Surjective ρ ∧
      (∀ f : ↥Q', ∃ g : ↥Q', (f : Additive (WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p]))) + g = 0) ∧
      (∀ σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
        ∀ (f : ↥Q') (g : WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p])),
          (∀ h : HB, g h = σ (Additive.toMul (f : Additive (WithConv (HB →ₐ[B] AlgebraicClosure ℚ_[p]))) h)) →
            ∃ hg : Additive.ofMul g ∈ Q', ρ ⟨Additive.ofMul g, hg⟩ = σ • ρ f) := by
  classical

  obtain ⟨K, hKfin, hIK, hKmult, hKquot, b, a, r, ρ, κ, hrK, hrval, hρ, hκ, π, hπ, hπσ⟩ :=
    HopfAlgebra.exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer p hp2 N M hM hpM M₁ hM₁
      n hn hmult hquot ζ hζ u β hu huI hβ φ hφ₁ hφ₀ hdec

  obtain ⟨B, iB1, iB2, iB3, iB4, iB5, iB6, iB7, iB8, hBK, hBunit⟩ :=
    IntermediateField.exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup p K hKfin hIK

  have hunit : ∀ m k, ∃ wmk : Bˣ, algebraMap B (AlgebraicClosure ℚ_[p]) (wmk : B) = r m k := by
    intro m k
    obtain ⟨c, hc, hcr⟩ := hBunit (r m k) (hrK m k) (hrval m k)
    exact ⟨hc.unit, by rw [IsUnit.unit_spec]; exact hcr⟩
  choose w hw using hunit
  have hρ' : ∀ m k, ρ m k ^ p ^ N = algebraMap B (AlgebraicClosure ℚ_[p]) (w m k : B) := fun m k => by rw [hw, hρ]
  have hκ' : ∀ σ ∈ fixer p B, ∀ m k, σ (ρ m k) = ζ ^ κ σ m k * ρ m k := fun σ hσ m k => hκ σ (hBK σ hσ) m k
  have hπσ' : ∀ σ ∈ fixer p B, ∀ (i : Fin b → ZMod (p ^ N)) (l : Fin a → ZMod (p ^ N)),
      π (fun m => n σ • i m + ∑ k, κ σ m k • l k, l) = σ • π (i, l) := fun σ hσ => hπσ σ (hBK σ hσ)
  obtain ⟨HB, i1, i2, i3, i4, i5, Q', ρ', hsurj, hinv, hequiv⟩ :=
    exists_carrier_over_level p N hp2 M n hn ζ hζ B b a w ρ κ hρ' hκ' π hπ hπσ'
  exact ⟨B, iB1, iB2, iB3, iB4, iB5, iB6, iB7, iB8, HB, i1, i2, i3, i4, i5, Q', ρ', hsurj, hinv, hequiv⟩

end S_HopfAlgebra_exists_hopf_points_subquotient_of_unitKummer_over_etale_level
end P2MW
export P2MW.S_HopfAlgebra_exists_hopf_points_subquotient_of_unitKummer_over_etale_level (solution)
