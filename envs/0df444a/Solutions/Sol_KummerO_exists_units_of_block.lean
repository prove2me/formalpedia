-- Prove2me | solution 1 for KummerO.exists_units_of_block
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9667e39d-481f-58df-8a2d-ac7d1c40eb8d

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_HopfAlgebra_blockPieces_torsor_core
import Theorems.Thm_HopfAlgebra_exists_unit_pow_of_torsor_grading_nsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KummerO_exists_units_of_block

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

namespace Ws25.TorsorGrading
private theorem _root_.Ws25.TorsorGrading.exists_unit_pow_of_torsor_grading_nsmul
    {Λ : Type} [AddCommGroup Λ]
    {R T : Type} [CommRing R] [CommRing T] [Algebra R T]
    (hinj : Function.Injective (algebraMap R T))
    (L : Λ → Submodule R T)
    (hL0 : L 0 = Submodule.span R {(1 : T)})
    (hcyc : ∀ j, ∃ t : T, L j = Submodule.span R {t})
    (hmul : ∀ i j, ∀ x ∈ L i, ∀ y ∈ L j, x * y ∈ L (i + j))
    (htorsor : ∀ i j, L (i + j) ≤ Submodule.span R {z | ∃ x ∈ L i, ∃ y ∈ L j, z = x * y})
    (g : Λ) (Q : ℕ) (hgQ : Q • g = 0) :
    ∃ (t : T) (u : R), IsUnit u ∧ L g = Submodule.span R {t} ∧
      t ^ Q = algebraMap R T u ∧
      ∀ j : ℕ, L (j • g) = Submodule.span R {t ^ j} :=
  HopfAlgebra.exists_unit_pow_of_torsor_grading_nsmul hinj L hL0 hcyc hmul htorsor g Q hgQ

end Ws25.TorsorGrading
p2m_export "" "Ws25.TorsorGrading.exists_unit_pow_of_torsor_grading_nsmul"
namespace Ws25
namespace KummerO
namespace PointsDict

open WithConv

section Provider
variable (A : ValuationSubring (AlgebraicClosure ℚ)) (O : Type) [CommRing O] [Algebra O ↥A]

@[reducible] noncomputable def algebraQbar : Algebra O (AlgebraicClosure ℚ) :=
  ((algebraMap ↥A (AlgebraicClosure ℚ)).comp (algebraMap O ↥A)).toAlgebra

theorem isScalarTower_qbar : letI := algebraQbar A O; IsScalarTower O ↥A (AlgebraicClosure ℚ) :=
  letI := algebraQbar A O
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

end Provider

section Points

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {O : Type} [CommRing O] [Algebra O ↥A]
  [Algebra O (AlgebraicClosure ℚ)] [IsScalarTower O ↥A (AlgebraicClosure ℚ)]
variable (B : Type) [CommRing B] [Bialgebra O B]

omit [Bialgebra O B] in
theorem algebraMap_mem (x : O) : algebraMap O (AlgebraicClosure ℚ) x ∈ A := by
  rw [IsScalarTower.algebraMap_apply O ↥A (AlgebraicClosure ℚ)]
  exact (algebraMap O ↥A x).2

noncomputable abbrev jA : ↥A →ₐ[O] AlgebraicClosure ℚ := IsScalarTower.toAlgHom O ↥A (AlgebraicClosure ℚ)

omit [Bialgebra O B] in
theorem jA_apply (a : ↥A) : jA (A := A) (O := O) a = (a : AlgebraicClosure ℚ) := rfl

theorem apply_mem_of_moduleFinite {B : Type} [CommRing B] [Algebra O B] [Module.Finite O B]
    (f : B →ₐ[O] AlgebraicClosure ℚ) (h : B) : f h ∈ A := by
  classical
  have hOA : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ A := algebraMap_mem (A := A) (O := O)
  have hint : IsIntegral O (f h) := (Algebra.IsIntegral.isIntegral (R := O) h).map f
  obtain ⟨p, hpm, hpev⟩ := hint
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : A.valuation (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap O (AlgebraicClosure ℚ) (p.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpev
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree,
          algebraMap O (AlgebraicClosure ℚ) (p.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : A.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap O (AlgebraicClosure ℚ) (p.coeff i) * f h ^ i)
        < A.valuation (f h) ^ p.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (algebraMap O (AlgebraicClosure ℚ) (p.coeff i)) * A.valuation (f h) ^ i
        ≤ 1 * A.valuation (f h) ^ i := by
          apply mul_le_mul_left
          exact (A.valuation_le_one_iff _).mpr (hOA (p.coeff i))
      _ = A.valuation (f h) ^ i := one_mul _
      _ < A.valuation (f h) ^ p.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : A.valuation (f h ^ p.natDegree) < A.valuation (f h) ^ p.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

noncomputable def toQ (f : WithConv (B →ₐ[O] ↥A)) : WithConv (B →ₐ[O] AlgebraicClosure ℚ) :=
  toConv ((jA (A := A) (O := O)).comp (ofConv f))

theorem toQ_apply (f : WithConv (B →ₐ[O] ↥A)) (b : B) :
    ofConv (toQ B f) b = ((ofConv f b : ↥A) : AlgebraicClosure ℚ) := rfl

theorem toQ_injective : Function.Injective (toQ (A := A) (O := O) B) := by
  intro f g hfg
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  apply Subtype.ext
  have := congrArg (fun φ : WithConv (B →ₐ[O] AlgebraicClosure ℚ) => ofConv φ b) hfg
  exact this

theorem toQ_mul (f g : WithConv (B →ₐ[O] ↥A)) : toQ B (f * g) = toQ B f * toQ B g := by
  apply WithConv.ext
  show (jA (A := A) (O := O)).comp (ofConv (f * g)) = _
  rw [AlgHom.comp_convMul_distrib]
  rfl

theorem toQ_one : toQ (A := A) (O := O) B 1 = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  rw [toQ_apply]
  show (((1 : WithConv (B →ₐ[O] ↥A)) b : ↥A) : AlgebraicClosure ℚ) = (1 : WithConv (B →ₐ[O] AlgebraicClosure ℚ)) b
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, IsScalarTower.algebraMap_apply O ↥A (AlgebraicClosure ℚ)]
  rfl

theorem toQ_pow (f : WithConv (B →ₐ[O] ↥A)) (n : ℕ) : toQ B (f ^ n) = toQ B f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toQ_one]
  | succ n ih => rw [pow_succ, pow_succ, toQ_mul, ih]

noncomputable def ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] AlgebraicClosure ℚ)) : WithConv (B →ₐ[O] ↥A) :=
  toConv
    { toFun := fun b => ⟨ofConv φ b, apply_mem_of_moduleFinite (ofConv φ) b⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      commutes' := fun r => Subtype.ext (by
        show ofConv φ (algebraMap O B r) = ((algebraMap O ↥A r : ↥A) : AlgebraicClosure ℚ)
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O ↥A (AlgebraicClosure ℚ)]
        rfl) }

theorem ofQ_apply [Module.Finite O B] (φ : WithConv (B →ₐ[O] AlgebraicClosure ℚ)) (b : B) :
    ((ofConv (ofQ (A := A) B φ) b : ↥A) : AlgebraicClosure ℚ) = ofConv φ b := rfl

theorem toQ_ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] AlgebraicClosure ℚ)) : toQ B (ofQ (A := A) B φ) = φ := by
  apply WithConv.ext; apply AlgHom.ext; intro b; rfl

theorem ofQ_toQ [Module.Finite O B] (f : WithConv (B →ₐ[O] ↥A)) : ofQ (A := A) B (toQ B f) = f := by
  apply WithConv.ext; apply AlgHom.ext; intro b; apply Subtype.ext; rfl

noncomputable def pointsEquiv [Module.Finite O B] : WithConv (B →ₐ[O] ↥A) ≃ WithConv (B →ₐ[O] AlgebraicClosure ℚ) :=
  { toFun := toQ B
    invFun := ofQ (A := A) B
    left_inv := ofQ_toQ B
    right_inv := toQ_ofQ B }

theorem pointsEquiv_apply [Module.Finite O B] (f : WithConv (B →ₐ[O] ↥A)) : pointsEquiv (A := A) B f = toQ B f := rfl

theorem apply_eq_one_iff (f : WithConv (B →ₐ[O] ↥A)) (e : B) : ofConv f e = 1 ↔ ofConv (toQ B f) e = 1 := by
  rw [toQ_apply]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Subtype.ext h

theorem natCard_block_eq [Module.Finite O B] (e : B) :
    Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ofConv ψ e = 1} = Nat.card {φ : WithConv (B →ₐ[O] AlgebraicClosure ℚ) // ofConv φ e = 1} :=
  Nat.card_congr ((pointsEquiv (A := A) B).subtypeEquiv (fun f => apply_eq_one_iff B f e))

theorem forall_apply_eq_iff (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g : WithConv (B →ₐ[O] ↥A)) :
    (∀ b : B, ((ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((ofConv f b : ↥A) : AlgebraicClosure ℚ)) ↔
      ∀ b : B, ofConv (toQ B g) b = σ (ofConv (toQ B f) b) := Iff.rfl

end Points

end Ws25.KummerO.PointsDict

theorem KummerO.exists_units_of_block_of_gradings
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O]
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : Γℚ, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ ((ι x : ↥A) : AlgebraicClosure ℚ) = ((ι x : ↥A) : AlgebraicClosure ℚ))
    (B : Type) [CommRing B] [Algebra O B] [Module.IsTorsionFree O B]
    (e : B) (hidem : IsIdempotentElem e)
    (hne : ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1)
    (Λ : Type) [AddCommGroup Λ] (hΛq : ∀ g : Λ, q • g = 0)
    (Lf : Λ → Submodule O B)
    (hL0 : Lf 0 = Submodule.span O {e})
    (hcyc : ∀ j : Λ, ∃ t : B, Lf j = Submodule.span O {t})
    (htor : ∀ i j : Λ, Lf (i + j) ≤ Submodule.span O {z : B | ∃ x ∈ Lf i, ∃ y ∈ Lf j, z = x * y})
    (hmul : ∀ i j : Λ, ∀ x ∈ Lf i, ∀ y ∈ Lf j, x * y ∈ Lf (i + j))
    (hcomplete : ∀ x : B, x * e = x → x ∈ ⨆ j : Λ, Lf j) :
    ∃ (U β : Λ → AlgebraicClosure ℚ),
      (∀ g, A.valuation (U g) = 1) ∧
      (∀ g, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (U g) = U g) ∧
      (∀ g, (β g) ^ q = U g) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ) → (∀ g, σ (β g) = β g) →
        ∀ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1 →
          ∀ b : B, σ ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ) = ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ)) := by
  classical
  have hqp : q.Prime := Fact.out
  have hQpos : 0 < q := hqp.pos
  obtain ⟨ψa, hψa⟩ := hne
  have hεa : e ≠ 0 := by
    intro h
    rw [h, map_zero] at hψa
    exact zero_ne_one hψa

  let Ia : Ideal B := Ideal.span {1 - e}
  let mk : B →ₐ[O] B ⧸ Ia := Ideal.Quotient.mkₐ O Ia
  have hmk : ∀ x, mk x = Ideal.Quotient.mk Ia x := fun _ => rfl
  have hmk_surj : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective O Ia
  have hmkε : mk e = 1 := by
    rw [hmk, ← (Ideal.Quotient.mk Ia).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-1, by ring⟩
  have hmk_mul_ε : ∀ x, mk (x * e) = mk x := fun x => by rw [map_mul, hmkε, mul_one]
  have hker : ∀ x, mk x = 0 → ∃ z, x = z * (1 - e) := by
    intro x hx
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, hz.symm⟩
  have hinj : Function.Injective (algebraMap O (B ⧸ Ia)) := by
    intro o₁ o₂ h
    have h' : algebraMap O (B ⧸ Ia) (o₁ - o₂) = 0 := by rw [map_sub, h, sub_self]
    rw [← mk.commutes, Algebra.algebraMap_eq_smul_one] at h'
    obtain ⟨z, hz⟩ := hker _ h'
    have h2 : (o₁ - o₂) • e = 0 := by
      have := congrArg (· * e) hz
      rw [smul_mul_assoc, one_mul, mul_assoc, sub_mul, one_mul, hidem.eq, sub_self, mul_zero] at this
      exact this
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hεa

  let L : Λ → Submodule O (B ⧸ Ia) := fun j => (Lf j).map mk.toLinearMap
  have hL : ∀ j, L j = (Lf j).map mk.toLinearMap := fun _ => rfl
  have hmemL : ∀ {j} {y}, y ∈ L j ↔ ∃ x ∈ Lf j, mk x = y := by
    intro j y
    rw [hL, Submodule.mem_map]
    rfl
  have hmap_span : ∀ x : B, (Submodule.span O {x}).map mk.toLinearMap = Submodule.span O {mk x} := by
    intro x
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  have hL0' : L 0 = Submodule.span O {(1 : B ⧸ Ia)} := by
    rw [hL, hL0, hmap_span, hmkε]
  have hcyc' : ∀ j, ∃ t, L j = Submodule.span O {t} := by
    intro j
    obtain ⟨t, ht⟩ := hcyc j
    exact ⟨mk t, by rw [hL, ht, hmap_span]⟩
  have hmul' : ∀ i j, ∀ x ∈ L i, ∀ y ∈ L j, x * y ∈ L (i + j) := by
    intro i j x hx y hy
    obtain ⟨x', hx', rfl⟩ := hmemL.mp hx
    obtain ⟨y', hy', rfl⟩ := hmemL.mp hy
    exact hmemL.mpr ⟨x' * y', hmul i j x' hx' y' hy', map_mul mk x' y'⟩
  have htor' : ∀ i j, L (i + j) ≤ Submodule.span O {z | ∃ x ∈ L i, ∃ y ∈ L j, z = x * y} := by
    intro i j
    change (Lf (i + j)).map mk.toLinearMap ≤ _
    refine (Submodule.map_mono (htor i j)).trans ?_
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨mk x, hmemL.mpr ⟨x, hx, rfl⟩, mk y, hmemL.mpr ⟨y, hy, rfl⟩, map_mul mk x y⟩

  have heng : ∀ g : Λ, ∃ (t : B) (u : O), IsUnit u ∧ L g = Submodule.span O {mk t} ∧
      (mk t) ^ q = algebraMap O (B ⧸ Ia) u := by
    intro g
    obtain ⟨t', u, hu, hLg, htq, -⟩ :=
      Ws25.TorsorGrading.exists_unit_pow_of_torsor_grading_nsmul hinj L hL0' hcyc' hmul' htor' g q (hΛq g)
    obtain ⟨t, rfl⟩ := hmk_surj t'
    exact ⟨t, u, hu, hLg, htq⟩
  choose t u hu hLg htq using heng

  let uQ : Λ → AlgebraicClosure ℚ := fun g => ((ι (u g) : ↥A) : AlgebraicClosure ℚ)
  have huQ : ∀ g, uQ g = ((ι (u g) : ↥A) : AlgebraicClosure ℚ) := fun _ => rfl
  have huA : ∀ g, A.valuation (uQ g) = 1 := by
    intro g
    have hunitA : IsUnit (ι (u g)) := (hu g).map ι
    exact (ValuationSubring.valuation_eq_one_iff A _).mp hunitA
  have hufix : ∀ g, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (uQ g) = uQ g := fun g σ hσ => (hιfix σ).mp hσ (u g)
  have hu0 : ∀ g, uQ g ≠ 0 := by
    intro g h
    have h' := huA g
    rw [h, Valuation.map_zero] at h'
    exact zero_ne_one h'
  have hβex : ∀ g : Λ, ∃ β : AlgebraicClosure ℚ, β ^ q = uQ g := fun g => IsAlgClosed.exists_pow_nat_eq _ hQpos
  choose β hβ using hβex
  have hβ0 : ∀ g, β g ≠ 0 := by
    intro g h
    have h' := hβ g
    rw [h, zero_pow hQpos.ne'] at h'
    exact hu0 g h'.symm
  refine ⟨uQ, β, huA, hufix, hβ, ?_⟩
  intro σ hσ hσμ hσβ ψ hψ

  let φ : B →ₐ[O] ↥A := WithConv.ofConv ψ
  let ev : B →+* AlgebraicClosure ℚ := (algebraMap ↥A (AlgebraicClosure ℚ)).comp φ.toRingHom
  have hev : ∀ x, ev x = ((φ x : ↥A) : AlgebraicClosure ℚ) := fun _ => rfl
  have hφe : φ e = 1 := hψ
  have heve : ev e = 1 := by rw [hev, hφe]; rfl
  have hvan : ∀ x, mk x = 0 → ev x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hker x hx
    rw [map_mul, map_sub, map_one, heve, sub_self, mul_zero]
  have hcongr : ∀ x y, mk x = mk y → ev x = ev y := by
    intro x y hxy
    have h := hvan (x - y) (by rw [map_sub, hxy, sub_self])
    rwa [map_sub, sub_eq_zero] at h
  have hevalg : ∀ c : O, ev (algebraMap O B c) = ((ι c : ↥A) : AlgebraicClosure ℚ) := by
    intro c
    rw [hev, AlgHom.commutes, hιalg]
  have hψtq : ∀ g, (ev (t g)) ^ q = uQ g := by
    intro g
    rw [← map_pow]
    have h1 : mk ((t g) ^ q) = mk (algebraMap O B (u g)) := by rw [map_pow, htq g, mk.commutes]
    rw [hcongr _ _ h1, hevalg]
  have hσψt : ∀ g, σ (ev (t g)) = ev (t g) := by
    intro g
    have hζ : (ev (t g) / β g) ^ q = 1 := by
      rw [div_pow, hψtq g, hβ g, div_self (hu0 g)]
    have h1 : ev (t g) = (ev (t g) / β g) * β g := by rw [div_mul_cancel₀ _ (hβ0 g)]
    rw [h1, map_mul, hσμ _ hζ, hσβ g]
  have hpiece : ∀ (g : Λ) (x : B), x ∈ Lf g → σ (ev x) = ev x := by
    intro g x hx
    have hmx : mk x ∈ Submodule.span O {mk (t g)} := by
      rw [← hLg g]; exact hmemL.mpr ⟨x, hx, rfl⟩
    rw [Submodule.mem_span_singleton] at hmx
    obtain ⟨c, hc⟩ := hmx
    have hx' : ev x = ((ι c : ↥A) : AlgebraicClosure ℚ) * ev (t g) := by
      have h2 : mk x = mk (c • t g) := by rw [map_smul, hc]
      rw [hcongr _ _ h2, Algebra.smul_def, map_mul, hevalg]
    rw [hx', map_mul, hσψt g, (hιfix σ).mp hσ c]
  have hwhole : ∀ x : B, x ∈ ⨆ j : Λ, Lf j → σ (ev x) = ev x := by
    intro x hx
    refine Submodule.iSup_induction (fun j : Λ => Lf j) (motive := fun x => σ (ev x) = ev x) hx ?_ ?_ ?_
    · intro j x hx
      exact hpiece j x hx
    · show σ (ev 0) = ev 0
      rw [map_zero, map_zero]
    · intro x y hx hy
      show σ (ev (x + y)) = ev (x + y)
      rw [map_add, map_add, hx, hy]
  intro b
  have hsplit : ev b = ev (b * e) := hcongr _ _ (hmk_mul_ε b).symm
  show σ (ev b) = ev b
  rw [hsplit]
  exact hwhole _ (hcomplete _ (by rw [mul_assoc, hidem.eq]))

open Ws25.KummerO.PointsDict in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : Γℚ, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ ((ι x : ↥A) : AlgebraicClosure ℚ) = ((ι x : ↥A) : AlgebraicClosure ℚ))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛq : ∀ g : Λ, q • g = 0)
    (p₀ : B →ₐc[O] MonoidAlgebra O (Multiplicative Λ)) (hsurj : Function.Surjective p₀)
    (e : B) (hidem : IsIdempotentElem e) (hcounit : Coalgebra.counit (R := O) e = 0)
    (hcard : Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ e = 1} = Fintype.card Λ)
    (hne : ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1) :
    ∃ (U β : Λ → AlgebraicClosure ℚ),
      (∀ g, A.valuation (U g) = 1) ∧
      (∀ g, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (U g) = U g) ∧
      (∀ g, (β g) ^ q = U g) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ) → (∀ g, σ (β g) = β g) →
        ∀ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1 → ∀ b : B, σ ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ) = ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ)) := by
  classical

  letI : Algebra O (AlgebraicClosure ℚ) := algebraQbar A O
  haveI : IsScalarTower O ↥A (AlgebraicClosure ℚ) := isScalarTower_qbar A O
  haveI : FaithfulSMul O (AlgebraicClosure ℚ) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply hι
    rw [← hιalg, ← hιalg]
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply O ↥A (AlgebraicClosure ℚ), IsScalarTower.algebraMap_apply O ↥A (AlgebraicClosure ℚ)] at hxy
    exact hxy
  have hOA : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ A := fun x =>
    Ws25.KummerO.PointsDict.algebraMap_mem (A := A) (O := O) x

  have hcard' : Nat.card {ψ : WithConv (B →ₐ[O] AlgebraicClosure ℚ) // ψ e = 1} = Fintype.card Λ := by
    rw [← hcard]; exact (natCard_block_eq (A := A) B e).symm
  have hΛq' : ∀ g : Λ, (q ^ 1) • g = 0 := fun g => by rw [pow_one]; exact hΛq g
  obtain ⟨hL0, hcyc, htor, hmul, hcomplete⟩ :=
    HopfAlgebra.blockPieces_torsor_core q 1 Λ hΛq' A hA O hOA inferInstance hirr B p₀ hsurj e hidem hcard'
  haveI : Module.IsTorsionFree O B := inferInstance
  exact KummerO.exists_units_of_block_of_gradings q A O ι hι hιalg hιfix B e hidem hne Λ hΛq
    (fun j => HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j) hL0 hcyc htor hmul hcomplete

end S_KummerO_exists_units_of_block
end P2MW
export P2MW.S_KummerO_exists_units_of_block (solution)
