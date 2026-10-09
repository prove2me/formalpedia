-- Prove2me | solution 1 for MazurProof.EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:14:43.98375+00:00
-- url     : https://prove2.me/submissions/ce49346a-346e-4f07-bbcb-c136938b714d

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.EvenSexticNormPair =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.EvenSexticNormPair =====
section
/-!
# Full norm-pair and fake targets for an even sextic

For an even sextic, the full two-descent target remembers a pair
`(α,s)` satisfying `N(α)=s²`.  It is quotiented by

* `(β²,N(β))`, and
* `(q,q³)` for ground-field scalars.

Forgetting the second coordinate gives the usual fake square-class target.
This file develops that target algebra for abstract commutative groups.  The
only sextic-specific input is that the norm of a scalar is its sixth power.
No Picard group or Kummer exactness theorem is used here.
-/
namespace MazurProof.EvenSexticNormPair
noncomputable section
variable {A B : Type*} [CommGroup A] [CommGroup B]
@[simp] theorem norm_fst_eq_snd_sq (N : A →* B) (p : NormPair N) :
    N (fstHom N p) = sndHom N p ^ 2 :=
  p.2
/-- Membership in the fake gauge has the expected square-times-scalar
normal form.  This is subgroup plumbing, not an arithmetic input. -/
theorem mem_fakeGauge_iff_exists (e : B →* A) (a : A) :
    a ∈ fakeGauge e ↔
      ∃ β : A, ∃ q : B, a = β ^ 2 * e q := by
  constructor
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Subgroup.mem_sup.mp ha)
    obtain ⟨β, hβ⟩ := Subgroup.mem_square.mp hx
    obtain ⟨q, -, hq⟩ := hy
    refine ⟨β, q, ?_⟩
    rw [← hxy, ← hq, hβ, pow_two]
  · rintro ⟨β, q, rfl⟩
    apply Subgroup.mul_mem_sup
    · exact Subgroup.mem_square.mpr ⟨β, by simp [pow_two]⟩
    · exact Subgroup.mem_map_of_mem e trivial
@[simp] theorem forget_signPair
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (ε : B) (hε : ε ^ 2 = 1) :
    forget N e norm_scalar
        (QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N ε hε)) = 1 := by
  rw [forget_mk]
  exact map_one _
/-! ## The kernel of forgetting the norm root -/
theorem fstHom_normalize_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B)
    (hp : fstHom N p = β ^ 2 * e q) :
    fstHom N (normalize N e norm_scalar p β q) = 1 := by
  change fstHom N p / (β ^ 2 * e q) = 1
  rw [hp]
  simp
theorem fullClass_normalize
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B) :
    QuotientGroup.mk' (fullGauge N e norm_scalar) p =
      QuotientGroup.mk' (fullGauge N e norm_scalar)
        (normalize N e norm_scalar p β q) := by
  let g : NormPair N := chi N β * iota N e norm_scalar q
  have hg : g ∈ fullGauge N e norm_scalar := by
    apply Subgroup.mul_mem_sup
    · exact ⟨β, rfl⟩
    · exact ⟨q, rfl⟩
  have hgclass :
      QuotientGroup.mk' (fullGauge N e norm_scalar) g = 1 :=
    (QuotientGroup.eq_one_iff g).2 hg
  have hp : p = normalize N e norm_scalar p β q * g := by
    simp [normalize, g]
  calc
    QuotientGroup.mk' (fullGauge N e norm_scalar) p =
        QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q * g) := by
      exact congrArg
        (QuotientGroup.mk' (fullGauge N e norm_scalar)) hp
    _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q) *
        QuotientGroup.mk' (fullGauge N e norm_scalar) g := by
      rw [map_mul]
    _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q) := by
      rw [hgclass, mul_one]
theorem sndHom_normalize_sq_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B)
    (hp : fstHom N p = β ^ 2 * e q) :
    sndHom N (normalize N e norm_scalar p β q) ^ 2 = 1 := by
  have hnorm :=
    norm_fst_eq_snd_sq N
      (normalize N e norm_scalar p β q)
  rw [fstHom_normalize_eq_one N e norm_scalar p β q hp] at hnorm
  simpa using hnorm.symm
/-- The fibre of the full target over the trivial fake class consists of
classes represented by `(1, ε)` with `ε²=1`. -/
theorem forget_eq_one_iff_exists_signPair
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (z : FullTarget N e norm_scalar) :
    forget N e norm_scalar z = 1 ↔
      ∃ ε : B, ∃ hε : ε ^ 2 = 1,
        z = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N ε hε) := by
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (fullGauge N e norm_scalar) z
    have hfake :
        QuotientGroup.mk' (fakeGauge e) (fstHom N p) = 1 := by
      change QuotientGroup.mk' (fakeGauge e) p.1.1 = 1
      simpa only [forget_mk] using hz
    have hmem : fstHom N p ∈ fakeGauge e :=
      (QuotientGroup.eq_one_iff (fstHom N p)).1 hfake
    obtain ⟨β, q, hp⟩ :=
      (mem_fakeGauge_iff_exists e (fstHom N p)).1 hmem
    let r : NormPair N := normalize N e norm_scalar p β q
    have hrfst : fstHom N r = 1 :=
      fstHom_normalize_eq_one N e norm_scalar p β q hp
    have hrsq : sndHom N r ^ 2 = 1 :=
      sndHom_normalize_sq_eq_one N e norm_scalar p β q hp
    have hr :
        r = signPair N (sndHom N r) hrsq := by
      apply Subtype.ext
      apply Prod.ext
      · exact hrfst
      · rfl
    refine ⟨sndHom N r, hrsq, ?_⟩
    calc
      QuotientGroup.mk' (fullGauge N e norm_scalar) p =
          QuotientGroup.mk' (fullGauge N e norm_scalar) r :=
        fullClass_normalize N e norm_scalar p β q
      _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N (sndHom N r) hrsq) :=
        congrArg
          (QuotientGroup.mk' (fullGauge N e norm_scalar)) hr
  · rintro ⟨ε, hε, rfl⟩
    exact forget_signPair N e norm_scalar ε hε
/-- If the base group has only two square roots of one, the forgetting
kernel has at most the identity and one sign class. -/
theorem forget_eq_one_iff_eq_one_or_eq_sign
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (σ : B) (hσ : σ ^ 2 = 1)
    (sqOne : ∀ ε : B, ε ^ 2 = 1 → ε = 1 ∨ ε = σ)
    (z : FullTarget N e norm_scalar) :
    forget N e norm_scalar z = 1 ↔
      z = 1 ∨
        z = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N σ hσ) := by
  constructor
  · intro hz
    obtain ⟨ε, hε, hzε⟩ :=
      (forget_eq_one_iff_exists_signPair N e norm_scalar z).1 hz
    rcases sqOne ε hε with rfl | rfl
    · left
      rw [hzε]
      have hraw : signPair N 1 hε = 1 := by
        apply Subtype.ext
        ext <;> simp [signPair]
      rw [hraw]
      exact map_one _
    · exact Or.inr hzε
  · rintro (rfl | rfl)
    · exact map_one _
    · exact forget_signPair N e norm_scalar σ hσ
end
end MazurProof.EvenSexticNormPair
end

end

theorem solution : type_of% @MazurProof.EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign := @MazurProof.EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign
