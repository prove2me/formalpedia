-- Prove2me | solution 1 for HopfAlgebra.exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d09e19e9-6120-5a72-8a1f-c3cbe3522711

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Theorems.Thm_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple
import Theorems.Thm_Representation_centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step

set_option autoImplicit false

noncomputable section

namespace WildE72

variable (P : ValuationSubring (AlgebraicClosure ℚ))

local notation "𝔾" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem mem_decomp_of_mem_inertia {σ : 𝔾} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    σ ∈ P.decompositionSubgroup ℚ := by
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hσ
  exact x.2

theorem div_mem {σ : 𝔾} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) {z : AlgebraicClosure ℚ} (hz : z ≠ 0) :
    σ z / z ∈ P := by
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀,
    P.valuation_map_eq_of_mem_decompositionSubgroup (mem_decomp_of_mem_inertia P hσ) z,
    div_self ((map_ne_zero _).mpr hz)]

theorem div_ne_zero' {σ : 𝔾} {z : AlgebraicClosure ℚ} (hz : z ≠ 0) : σ z / z ≠ 0 :=
  div_ne_zero ((map_ne_zero σ).mpr hz) hz

noncomputable def resCocycle (σ : 𝔾) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (z : AlgebraicClosure ℚ) (hz : z ≠ 0) :
    IsLocalRing.ResidueField ↥P :=
  IsLocalRing.residue ↥P ⟨σ z / z, div_mem P hσ hz⟩

theorem residue_map_eq {σ : 𝔾} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (a : ↥P) :
    IsLocalRing.residue ↥P ⟨σ a, (P.valuation_sub_lt_one_of_mem_inertiaSubgroupIn hσ a.2).1⟩ =
      IsLocalRing.residue ↥P a := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact (P.valuation_sub_lt_one_of_mem_inertiaSubgroupIn hσ a.2).2

theorem resCocycle_mul {σ τ : 𝔾} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    {z : AlgebraicClosure ℚ} (hz : z ≠ 0) :
    resCocycle P (σ * τ) ((P.inertiaSubgroupIn ℚ).mul_mem hσ hτ) z hz =
      resCocycle P σ hσ z hz * resCocycle P τ hτ z hz := by

  have hσz : σ z ≠ 0 := (map_ne_zero σ).mpr hz
  have hcoc : (σ * τ) z / z = σ (τ z / z) * (σ z / z) := by
    rw [AlgEquiv.mul_apply, map_div₀]
    field_simp
  unfold resCocycle
  rw [← map_mul]
  have hmem : σ (τ z / z) ∈ P := (P.valuation_sub_lt_one_of_mem_inertiaSubgroupIn hσ (div_mem P hτ hz)).1
  have : (⟨(σ * τ) z / z, div_mem P ((P.inertiaSubgroupIn ℚ).mul_mem hσ hτ) hz⟩ : ↥P) =
      ⟨σ (τ z / z), hmem⟩ * ⟨σ z / z, div_mem P hσ hz⟩ := Subtype.ext hcoc
  rw [this, map_mul, map_mul, mul_comm, residue_map_eq P hσ ⟨τ z / z, div_mem P hτ hz⟩]

theorem resCocycle_one {z : AlgebraicClosure ℚ} (hz : z ≠ 0) :
    resCocycle P 1 (P.inertiaSubgroupIn ℚ).one_mem z hz = 1 := by
  unfold resCocycle
  have : (⟨(1 : 𝔾) z / z, div_mem P (P.inertiaSubgroupIn ℚ).one_mem hz⟩ : ↥P) = 1 :=
    Subtype.ext (by simp [hz])
  rw [this, map_one]

noncomputable def resHom (z : AlgebraicClosure ℚ) (hz : z ≠ 0) :
    ↥(P.inertiaSubgroupIn ℚ) →* IsLocalRing.ResidueField ↥P where
  toFun σ := resCocycle P σ.1 σ.2 z hz
  map_one' := resCocycle_one P hz
  map_mul' σ τ := resCocycle_mul P σ.2 τ.2 hz

def IsWild (σ : 𝔾) : Prop := ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits

theorem isWild_iff_resHom (σ : ↥(P.inertiaSubgroupIn ℚ)) :
    IsWild P σ.1 ↔ ∀ (z : AlgebraicClosure ℚ) (hz : z ≠ 0), resHom P z hz σ = 1 := by
  constructor
  · intro h z hz
    show IsLocalRing.residue ↥P _ = 1
    rw [← (IsLocalRing.residue ↥P).map_one, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    have := h z hz
    rw [ValuationSubring.mem_nonunits_iff] at this
    simpa [div_eq_mul_inv] using this
  · intro h z hz
    have h1 := h z hz
    change IsLocalRing.residue ↥P _ = 1 at h1
    rw [← (IsLocalRing.residue ↥P).map_one, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff] at h1
    rw [ValuationSubring.mem_nonunits_iff]
    simpa [div_eq_mul_inv] using h1

theorem valuation_div_eq_one {σ : 𝔾} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) {z : AlgebraicClosure ℚ} (hz : z ≠ 0) :
    P.valuation (σ z / z) = 1 := by
  rw [map_div₀, P.valuation_map_eq_of_mem_decompositionSubgroup (mem_decomp_of_mem_inertia P hσ) z,
    div_self ((map_ne_zero _).mpr hz)]

theorem resHom_ne_zero (z : AlgebraicClosure ℚ) (hz : z ≠ 0) (σ : ↥(P.inertiaSubgroupIn ℚ)) :
    resHom P z hz σ ≠ 0 := by
  show IsLocalRing.residue ↥P _ ≠ 0
  rw [Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  simp only [valuation_div_eq_one P σ.2 hz, lt_self_iff_false, not_false_eq_true]

theorem resHom_inv (z : AlgebraicClosure ℚ) (hz : z ≠ 0) (σ : ↥(P.inertiaSubgroupIn ℚ)) :
    resHom P z hz σ⁻¹ = (resHom P z hz σ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

theorem isWild_commutator (σ τ : ↥(P.inertiaSubgroupIn ℚ)) :
    IsWild P (σ * τ * σ⁻¹ * τ⁻¹ : ↥(P.inertiaSubgroupIn ℚ)).1 := by
  rw [isWild_iff_resHom]
  intro z hz
  have ha := resHom_ne_zero P z hz σ
  have hb := resHom_ne_zero P z hz τ
  rw [map_mul, map_mul, map_mul, resHom_inv, resHom_inv]
  field_simp

end WildE72

namespace WildE72

theorem exists_pow_fixes_points {p : ℕ} (hp : p.Prime)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H]
    [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hwild : IsWild P σ) :
    ∃ a : ℕ, ∀ (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (h : H),
      (σ ^ (p ^ a)) (f h) = f h := by
  classical

  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := GaloisRep.ratLocalizedAt p) (M := H)
  haveI : Fintype (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) := Fintype.ofFinite _

  let T : Finset (AlgebraicClosure ℚ) :=
    (Finset.univ (α := WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) ×ˢ S).image
      (fun fh => fh.1 fh.2)
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ (T : Set (AlgebraicClosure ℚ))
  haveI hAC : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.instIsAlgClosure ℚ
    rfl
    rfl
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := hAC.isAlgebraic
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal (R := ℚ) (K := AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ ↥F (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ E := normalClosure.is_finiteDimensional ℚ ↥F (AlgebraicClosure ℚ)
  haveI : Normal ℚ E := normalClosure.normal ℚ ↥F (AlgebraicClosure ℚ)
  obtain ⟨a, ha⟩ := ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild hp P hP hwild E
  refine ⟨a, fun f h => ha (f h) ?_⟩

  apply IntermediateField.le_normalClosure F
  have hgen : ∀ x ∈ S, f x ∈ F := fun x hx =>
    IntermediateField.subset_adjoin ℚ _ (Finset.mem_image.mpr ⟨(f, x), Finset.mem_product.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩)
  have hh : h ∈ Submodule.span (GaloisRep.ratLocalizedAt p) (S : Set H) := by rw [hS]; trivial
  induction hh using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => rw [map_zero]; exact F.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
  | smul c x _ hx =>
      rw [map_smul]
      have hsm : c • (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) x =
          algebraMap ℚ (AlgebraicClosure ℚ) (c : ℚ) * (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) x := by
        rw [show c • (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) x =
            (c : ℚ) • (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) x from rfl,
          Algebra.smul_def]
      rw [hsm]
      exact F.mul_mem (F.algebraMap_mem _) hx

end WildE72

namespace StepLineE72

universe u₁ u₂ u₃

def Pt (R₀ : Type u₁) [CommRing R₀] (H : Type u₂) [CommRing H] [HopfAlgebra R₀ H]
    (L : Type u₃) [Field L] [Algebra R₀ L] (p : ℕ) : Type (max u₂ u₃) :=
  WithConv (H →ₐ[R₀] L)

section Basic

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}

noncomputable scoped instance : CommMonoid (Pt R₀ H L p) :=
  inferInstanceAs (CommMonoid (WithConv (H →ₐ[R₀] L)))

def ofPt : Pt R₀ H L p ≃* WithConv (H →ₐ[R₀] L) := MulEquiv.refl _

def postComp (σ : L →ₐ[R₀] L) : Pt R₀ H L p →* Pt R₀ H L p where
  toFun f := (WithConv.toConv (σ.comp (WithConv.ofConv (ofPt f))) : WithConv (H →ₐ[R₀] L))
  map_one' := by
    apply WithConv.ofConv_injective
    show σ.comp (WithConv.ofConv (1 : WithConv (H →ₐ[R₀] L))) = WithConv.ofConv (1 : WithConv (H →ₐ[R₀] L))
    rw [AlgHom.convOne_def, WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
    congr 1
    apply AlgHom.ext
    intro x
    simp
  map_mul' f g := by
    apply WithConv.ofConv_injective
    show σ.comp (WithConv.ofConv ((ofPt f) * (ofPt g))) = _
    rw [AlgHom.comp_convMul_distrib]
    rfl

theorem postComp_apply (σ : L →ₐ[R₀] L) (f : Pt R₀ H L p) (h : H) :
    (ofPt (postComp σ f) : WithConv (H →ₐ[R₀] L)) h = σ ((ofPt f : WithConv (H →ₐ[R₀] L)) h) := rfl

variable [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]

omit hp in

theorem pow_p (f : Pt R₀ H L p) : f ^ p = 1 := hM.out f

theorem mul_pow_sub_one_self (f : Pt R₀ H L p) : f * f ^ (p - 1) = 1 := by
  rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le, pow_p]

noncomputable scoped instance : CommGroup (Pt R₀ H L p) :=
  commGroupOfIsUnit fun f => IsUnit.of_mul_eq_one _ (mul_pow_sub_one_self f)

theorem inv_eq_pow (f : Pt R₀ H L p) : f⁻¹ = f ^ (p - 1) :=
  inv_eq_of_mul_eq_one_right (mul_pow_sub_one_self f)

def sg (S : Submonoid (Pt R₀ H L p)) : Subgroup (Pt R₀ H L p) where
  toSubmonoid := S
  inv_mem' {f} hf := by
    have hf' : f ∈ S := hf
    show f⁻¹ ∈ S
    rw [inv_eq_pow]
    exact pow_mem hf' _

@[scoped simp] theorem mem_sg (S : Submonoid (Pt R₀ H L p)) (f : Pt R₀ H L p) : f ∈ sg S ↔ f ∈ S := Iff.rfl

end Basic

section Step

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}
  [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]
  (K K' : Submonoid (Pt R₀ H L p))

abbrev V : Type (max u₂ u₃) := ↥(sg K') ⧸ (sg K).subgroupOf (sg K')

example : CommGroup (V K K') := inferInstance

def cls (f : Pt R₀ H L p) (hf : f ∈ K') : V K K' := QuotientGroup.mk ⟨f, hf⟩

theorem cls_eq_cls_iff {f g : Pt R₀ H L p} (hf : f ∈ K') (hg : g ∈ K') :
    cls K K' f hf = cls K K' g hg ↔ ∃ k ∈ K, g = f * k := by
  rw [cls, cls, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, mem_sg]
  change f⁻¹ * g ∈ K ↔ _
  constructor
  · intro h
    exact ⟨f⁻¹ * g, h, by rw [mul_inv_cancel_left]⟩
  · rintro ⟨k, hk, rfl⟩
    rwa [inv_mul_cancel_left]

theorem cls_mul {f g : Pt R₀ H L p} (hf : f ∈ K') (hg : g ∈ K') :
    cls K K' (f * g) (K'.mul_mem hf hg) = cls K K' f hf * cls K K' g hg := rfl

theorem cls_surjective (v : V K K') : ∃ (f : Pt R₀ H L p) (hf : f ∈ K'), cls K K' f hf = v := by
  induction v using QuotientGroup.induction_on with
  | H z => exact ⟨z.1, z.2, rfl⟩

theorem cls_eq_one_iff {f : Pt R₀ H L p} (hf : f ∈ K') : cls K K' f hf = 1 ↔ f ∈ K := by
  rw [cls, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem pow_p_V (v : V K K') : v ^ p = 1 := by
  obtain ⟨f, hf, rfl⟩ := cls_surjective K K' v
  rw [cls, ← QuotientGroup.mk_pow, show (⟨f, hf⟩ : ↥(sg K')) ^ p = 1 from Subtype.ext (pow_p f),
    QuotientGroup.mk_one]

noncomputable scoped instance : Module (ZMod p) (Additive (V K K')) :=
  AddCommGroup.zmodModule (fun v => by
    change Additive.ofMul ((Additive.toMul v) ^ p) = 0
    rw [pow_p_V]; rfl)

end Step

section Operators

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}
  [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]
  (K K' : Submonoid (Pt R₀ H L p))

def stepMap (φ : Pt R₀ H L p →* Pt R₀ H L p) (hK : ∀ f ∈ K, φ f ∈ K) (hK' : ∀ f ∈ K', φ f ∈ K') :
    V K K' →* V K K' :=
  QuotientGroup.map _ _ ((φ.comp (sg K').subtype).codRestrict (sg K') (fun x => hK' x.1 x.2)) (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hK _ hx)

theorem stepMap_cls (φ : Pt R₀ H L p →* Pt R₀ H L p) (hK : ∀ f ∈ K, φ f ∈ K)
    (hK' : ∀ f ∈ K', φ f ∈ K') (f : Pt R₀ H L p) (hf : f ∈ K') :
    stepMap K K' φ hK hK' (cls K K' f hf) = cls K K' (φ f) (hK' f hf) := rfl

def stepLin (φ : Pt R₀ H L p →* Pt R₀ H L p) (hK : ∀ f ∈ K, φ f ∈ K) (hK' : ∀ f ∈ K', φ f ∈ K') :
    Additive (V K K') →ₗ[ZMod p] Additive (V K K') :=
  (MonoidHom.toAdditive (stepMap K K' φ hK hK')).toZModLinearMap p

theorem stepLin_apply (φ : Pt R₀ H L p →* Pt R₀ H L p) (hK : ∀ f ∈ K, φ f ∈ K)
    (hK' : ∀ f ∈ K', φ f ∈ K') (v : V K K') :
    stepLin K K' φ hK hK' (Additive.ofMul v) = Additive.ofMul (stepMap K K' φ hK hK' v) := rfl

theorem submodule_eq_bot_or_top (hKK' : K ≤ K')
    (Φ : Set (Pt R₀ H L p →* Pt R₀ H L p))
    (hΦK : ∀ φ ∈ Φ, ∀ f ∈ K, φ f ∈ K) (hΦK' : ∀ φ ∈ Φ, ∀ f ∈ K', φ f ∈ K')
    (hstep : ∀ S : Submonoid (Pt R₀ H L p), K ≤ S → S ≤ K' →
      (∀ φ ∈ Φ, ∀ f ∈ S, φ f ∈ S) → S = K ∨ S = K')
    (W : Submodule (ZMod p) (Additive (V K K')))
    (hW : ∀ φ (hφ : φ ∈ Φ), ∀ v ∈ W, stepLin K K' φ (hΦK φ hφ) (hΦK' φ hφ) v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical

  let S : Submonoid (Pt R₀ H L p) :=
    { carrier := {f | ∃ hf : f ∈ K', Additive.ofMul (cls K K' f hf) ∈ W}
      one_mem' := ⟨K'.one_mem, by
        have : cls K K' 1 K'.one_mem = 1 := (cls_eq_one_iff K K' K'.one_mem).mpr K.one_mem
        rw [this]; exact W.zero_mem⟩
      mul_mem' := by
        rintro f g ⟨hf, hfW⟩ ⟨hg, hgW⟩
        refine ⟨K'.mul_mem hf hg, ?_⟩
        rw [cls_mul K K' hf hg]
        exact W.add_mem hfW hgW }
  have hKS : K ≤ S := fun f hf =>
    ⟨hKK' hf, by rw [(cls_eq_one_iff K K' (hKK' hf)).mpr hf]; exact W.zero_mem⟩
  have hSK' : S ≤ K' := fun f ⟨hf, _⟩ => hf
  have hSstab : ∀ φ ∈ Φ, ∀ f ∈ S, φ f ∈ S := by
    rintro φ hφ f ⟨hf, hfW⟩
    exact ⟨hΦK' φ hφ f hf, by
      have := hW φ hφ _ hfW
      rwa [stepLin_apply, stepMap_cls] at this⟩
  rcases hstep S hKS hSK' hSstab with hS | hS
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨f, hf, hfv⟩ := cls_surjective K K' (Additive.toMul v)
    have hfS : f ∈ S := ⟨hf, by rw [hfv]; exact hv⟩
    rw [hS] at hfS
    have h1 : cls K K' f hf = 1 := (cls_eq_one_iff K K' hf).mpr hfS
    have h2 : Additive.toMul v = 1 := by rw [← hfv]; exact h1
    calc v = Additive.ofMul (Additive.toMul v) := rfl
      _ = Additive.ofMul 1 := by rw [h2]
      _ = 0 := rfl
  · right
    rw [Submodule.eq_top_iff']
    intro v
    obtain ⟨f, hf, hfv⟩ := cls_surjective K K' (Additive.toMul v)
    have hfS : f ∈ S := by rw [hS]; exact hf
    obtain ⟨hf', hfW⟩ := hfS
    have : v = Additive.ofMul (cls K K' f hf') := by rw [hfv]; rfl
    rw [this]; exact hfW

theorem card_V_mul (hKK' : K ≤ K') [Finite (Pt R₀ H L p)] :
    Nat.card (V K K') * Nat.card K = Nat.card K' := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((sg K).subgroupOf (sg K'))
  have e1 : Nat.card ↥((sg K).subgroupOf (sg K')) = Nat.card K := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show sg K ≤ sg K' from hKK')).toEquiv]; rfl
  have e2 : Nat.card ↥(sg K') = Nat.card K' := rfl
  have h' : Nat.card (V K K') * Nat.card ↥((sg K).subgroupOf (sg K')) = Nat.card ↥(sg K') := h.symm
  rw [e1, e2] at h'
  exact h'

end Operators

section Rep

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}
  [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]
  (K K' : Submonoid (Pt R₀ H L p))

theorem cls_congr {f g : Pt R₀ H L p} (hf : f ∈ K') (hg : g ∈ K') (h : f = g) :
    cls K K' f hf = cls K K' g hg := by subst h; rfl

theorem stepLin_ofMul_cls (φ : Pt R₀ H L p →* Pt R₀ H L p) (hK : ∀ f ∈ K, φ f ∈ K)
    (hK' : ∀ f ∈ K', φ f ∈ K') (f : Pt R₀ H L p) (hf : f ∈ K') :
    stepLin K K' φ hK hK' (Additive.ofMul (cls K K' f hf)) = Additive.ofMul (cls K K' (φ f) (hK' f hf)) :=
  rfl

theorem exists_eq_ofMul_cls (v : Additive (V K K')) :
    ∃ (f : Pt R₀ H L p) (hf : f ∈ K'), v = Additive.ofMul (cls K K' f hf) := by
  obtain ⟨f, hf, h⟩ := cls_surjective K K' (Additive.toMul v)
  exact ⟨f, hf, by rw [h]; rfl⟩

variable {Γ : Type*} [Group Γ] (τ : Γ →* (L →ₐ[R₀] L))
  (hK : ∀ γ : Γ, ∀ f ∈ K, postComp (p := p) (τ γ) f ∈ K)
  (hK' : ∀ γ : Γ, ∀ f ∈ K', postComp (p := p) (τ γ) f ∈ K')

theorem postComp_one_apply (f : Pt R₀ H L p) : postComp (p := p) (1 : L →ₐ[R₀] L) f = f := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rfl

theorem postComp_mul_apply (σ σ' : L →ₐ[R₀] L) (f : Pt R₀ H L p) :
    postComp (p := p) (σ * σ') f = postComp σ (postComp σ' f) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rfl

def rep : Representation (ZMod p) Γ (Additive (V K K')) where
  toFun γ := stepLin K K' (postComp (τ γ)) (hK γ) (hK' γ)
  map_one' := by
    apply LinearMap.ext
    intro v
    obtain ⟨f, hf, rfl⟩ := exists_eq_ofMul_cls K K' v
    rw [stepLin_ofMul_cls]
    show Additive.ofMul _ = Additive.ofMul _
    congr 1
    exact cls_congr K K' _ _ (by rw [map_one, postComp_one_apply])
  map_mul' γ γ' := by
    apply LinearMap.ext
    intro v
    obtain ⟨f, hf, rfl⟩ := exists_eq_ofMul_cls K K' v
    show stepLin K K' _ _ _ _ = stepLin K K' _ _ _ (stepLin K K' _ _ _ _)
    rw [stepLin_ofMul_cls, stepLin_ofMul_cls, stepLin_ofMul_cls]
    congr 1
    exact cls_congr K K' _ _ (by rw [map_mul, postComp_mul_apply])

theorem rep_apply_ofMul_cls (γ : Γ) (f : Pt R₀ H L p) (hf : f ∈ K') :
    rep K K' τ hK hK' γ (Additive.ofMul (cls K K' f hf)) =
      Additive.ofMul (cls K K' (postComp (τ γ) f) (hK' γ f hf)) := rfl

theorem rep_simple (hKK' : K ≤ K')
    (hstep : ∀ S : Submonoid (Pt R₀ H L p), K ≤ S → S ≤ K' →
      (∀ γ : Γ, ∀ f ∈ S, postComp (p := p) (τ γ) f ∈ S) → S = K ∨ S = K')
    (W : Submodule (ZMod p) (Additive (V K K')))
    (hW : ∀ (γ : Γ) (v : Additive (V K K')), v ∈ W → rep K K' τ hK hK' γ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  refine submodule_eq_bot_or_top K K' hKK' (Set.range fun γ : Γ => postComp (p := p) (τ γ))
    (by rintro _ ⟨γ, rfl⟩; exact hK γ) (by rintro _ ⟨γ, rfl⟩; exact hK' γ)
    (fun S h1 h2 h3 => hstep S h1 h2 (fun γ f hf => h3 _ ⟨γ, rfl⟩ f hf)) W ?_
  rintro _ ⟨γ, rfl⟩ v hv
  exact hW γ v hv

end Rep

section Line

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}
  [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]
  (K K' : Submonoid (Pt R₀ H L p))
  {Γ : Type*} [Group Γ] (τ : Γ →* (L →ₐ[R₀] L))
  (hK : ∀ γ : Γ, ∀ f ∈ K, postComp (p := p) (τ γ) f ∈ K)
  (hK' : ∀ γ : Γ, ∀ f ∈ K', postComp (p := p) (τ γ) f ∈ K')

abbrev Comm : Subalgebra (ZMod p) (Module.End (ZMod p) (Additive (V K K'))) :=
  Subalgebra.centralizer (ZMod p)
    (Set.range (rep K K' τ hK hK' : Γ → Module.End (ZMod p) (Additive (V K K'))))

open Classical in

def act (a : Comm K K' τ hK hK') (f : Pt R₀ H L p) : Pt R₀ H L p :=
  if hf : f ∈ K' then
    (exists_eq_ofMul_cls K K' ((a : Module.End (ZMod p) (Additive (V K K'))) (Additive.ofMul (cls K K' f hf)))).choose
  else 1

theorem act_mem (a : Comm K K' τ hK hK') (f : Pt R₀ H L p) (hf : f ∈ K') : act K K' τ hK hK' a f ∈ K' := by
  unfold act
  rw [dif_pos hf]
  exact (exists_eq_ofMul_cls K K' _).choose_spec.choose

theorem ofMul_cls_act (a : Comm K K' τ hK hK') (f : Pt R₀ H L p) (hf : f ∈ K') :
    Additive.ofMul (cls K K' (act K K' τ hK hK' a f) (act_mem K K' τ hK hK' a f hf)) =
      (a : Module.End (ZMod p) (Additive (V K K'))) (Additive.ofMul (cls K K' f hf)) := by
  have h := (exists_eq_ofMul_cls K K'
    ((a : Module.End (ZMod p) (Additive (V K K'))) (Additive.ofMul (cls K K' f hf)))).choose_spec.choose_spec
  refine (Eq.trans ?_ h.symm)
  congr 1
  exact cls_congr K K' _ _ (by unfold act; rw [dif_pos hf])

theorem exists_mul_of_cls_eq {f g : Pt R₀ H L p} (hf : f ∈ K') (hg : g ∈ K')
    (h : Additive.ofMul (cls K K' f hf) = Additive.ofMul (cls K K' g hg)) : ∃ k ∈ K, g = f * k :=
  (cls_eq_cls_iff K K' hf hg).mp (Additive.ofMul.injective h)

theorem act_descends (hKK' : K ≤ K') (a : Comm K K' τ hK hK') (f : Pt R₀ H L p) (hf : f ∈ K')
    (k : Pt R₀ H L p) (hk : k ∈ K) :
    ∃ k' ∈ K, act K K' τ hK hK' a (f * k) = act K K' τ hK hK' a f * k' := by
  have hfk : f * k ∈ K' := K'.mul_mem hf (hKK' hk)
  have h1 := ofMul_cls_act K K' τ hK hK' a f hf
  have h2 := ofMul_cls_act K K' τ hK hK' a (f * k) hfk
  apply exists_mul_of_cls_eq K K' (act_mem K K' τ hK hK' a f hf) (act_mem K K' τ hK hK' a (f * k) hfk)
  rw [h1, h2]
  congr 2
  exact (cls_eq_cls_iff K K' hf hfk).mpr ⟨k, hk, rfl⟩

theorem act_mul_pt (a : Comm K K' τ hK hK') (f g : Pt R₀ H L p) (hf : f ∈ K') (hg : g ∈ K') :
    ∃ k ∈ K, act K K' τ hK hK' a (f * g) = act K K' τ hK hK' a f * act K K' τ hK hK' a g * k := by
  have hfg : f * g ∈ K' := K'.mul_mem hf hg
  have haf := act_mem K K' τ hK hK' a f hf
  have hag := act_mem K K' τ hK hK' a g hg
  have h1 := ofMul_cls_act K K' τ hK hK' a f hf
  have h2 := ofMul_cls_act K K' τ hK hK' a g hg
  have h3 := ofMul_cls_act K K' τ hK hK' a (f * g) hfg
  apply exists_mul_of_cls_eq K K' (K'.mul_mem haf hag) (act_mem K K' τ hK hK' a (f * g) hfg)
  rw [cls_mul K K' haf hag, ofMul_mul, h1, h2, h3, cls_mul K K' hf hg, ofMul_mul, map_add]

theorem act_add (a b : Comm K K' τ hK hK') (f : Pt R₀ H L p) (hf : f ∈ K') :
    ∃ k ∈ K, act K K' τ hK hK' (a + b) f = act K K' τ hK hK' a f * act K K' τ hK hK' b f * k := by
  have ha := act_mem K K' τ hK hK' a f hf
  have hb := act_mem K K' τ hK hK' b f hf
  have h1 := ofMul_cls_act K K' τ hK hK' a f hf
  have h2 := ofMul_cls_act K K' τ hK hK' b f hf
  have h3 := ofMul_cls_act K K' τ hK hK' (a + b) f hf
  apply exists_mul_of_cls_eq K K' (K'.mul_mem ha hb) (act_mem K K' τ hK hK' (a + b) f hf)
  rw [cls_mul K K' ha hb, ofMul_mul, h1, h2, h3, Subalgebra.coe_add, LinearMap.add_apply]

theorem act_mul (a b : Comm K K' τ hK hK') (f : Pt R₀ H L p) (hf : f ∈ K') :
    ∃ k ∈ K, act K K' τ hK hK' (a * b) f = act K K' τ hK hK' a (act K K' τ hK hK' b f) * k := by
  have hb := act_mem K K' τ hK hK' b f hf
  have hab := act_mem K K' τ hK hK' a _ hb
  have h1 := ofMul_cls_act K K' τ hK hK' b f hf
  have h2 := ofMul_cls_act K K' τ hK hK' a _ hb
  have h3 := ofMul_cls_act K K' τ hK hK' (a * b) f hf
  apply exists_mul_of_cls_eq K K' hab (act_mem K K' τ hK hK' (a * b) f hf)
  rw [h2, h1, h3, Subalgebra.coe_mul, Module.End.mul_apply]

theorem act_one (f : Pt R₀ H L p) (hf : f ∈ K') : ∃ k ∈ K, act K K' τ hK hK' 1 f = f * k := by
  have h3 := ofMul_cls_act K K' τ hK hK' 1 f hf
  apply exists_mul_of_cls_eq K K' hf (act_mem K K' τ hK hK' 1 f hf)
  rw [h3, Subalgebra.coe_one, Module.End.one_apply]

theorem act_equivariant (a : Comm K K' τ hK hK') (γ : Γ) (f : Pt R₀ H L p) (hf : f ∈ K') :
    ∃ k ∈ K, postComp (τ γ) (act K K' τ hK hK' a f) = act K K' τ hK hK' a (postComp (τ γ) f) * k := by
  have hσf := hK' γ f hf
  have haf := act_mem K K' τ hK hK' a f hf
  have h1 := ofMul_cls_act K K' τ hK hK' a f hf
  have h2 := ofMul_cls_act K K' τ hK hK' a _ hσf
  apply exists_mul_of_cls_eq K K' (act_mem K K' τ hK hK' a _ hσf) (hK' γ _ haf)
  rw [h2, ← rep_apply_ofMul_cls K K' τ hK hK' γ f hf, ← rep_apply_ofMul_cls K K' τ hK hK' γ _ haf, h1]
  have hc : (a : Module.End (ZMod p) (Additive (V K K'))) * rep K K' τ hK hK' γ =
      rep K K' τ hK hK' γ * (a : Module.End (ZMod p) (Additive (V K K'))) :=
    ((Subalgebra.mem_centralizer_iff (ZMod p)).mp a.2 _ ⟨γ, rfl⟩).symm
  exact LinearMap.congr_fun hc (Additive.ofMul (cls K K' f hf))

end Line

section Unipotent

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [Finite k] [CharP k p]
  {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V]

omit hp [Finite k] [CharP k p] [Finite V] [Nontrivial V] in
theorem comm_of_commutator_ker (ρ : Representation k Γ V)
    (h : ∀ g h : Γ, ρ (g * h * g⁻¹ * h⁻¹) = 1) (g g' : Γ) : ρ g * ρ g' = ρ g' * ρ g := by
  have h1 : g * g' = (g * g' * g⁻¹ * g'⁻¹) * g' * g := by group
  have := congrArg ρ h1
  rw [map_mul, map_mul, map_mul, h, one_mul] at this
  exact this

theorem rep_comm_of_normal_unipotent (ρ : Representation k Γ V)
    (hsimple : ∀ W : Submodule k V, (∀ (g : Γ) (v : V), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Subgroup Γ) [hWn : W.Normal]
    (hW : ∀ w ∈ W, ∃ a : ℕ, ρ (w ^ (p ^ a)) = 1)
    (hcommW : ∀ g h : Γ, g * h * g⁻¹ * h⁻¹ ∈ W) :
    ∀ g h : Γ, ρ g * ρ h = ρ h * ρ g := by
  classical
  haveI : Module.Finite k V := Module.Finite.of_finite
  haveI : Finite (V →ₗ[k] V) := Finite.of_injective (fun f : V →ₗ[k] V => (f : V → V)) DFunLike.coe_injective

  let φ : Γ →* (V →ₗ[k] V)ˣ := ρ.asGroupHom
  let Δ : Subgroup (V →ₗ[k] V)ˣ := φ.range
  haveI : Finite Δ := inferInstance
  let ρ' : Representation k Δ V := (Units.coeHom (V →ₗ[k] V)).comp Δ.subtype
  have hρ' : ∀ g : Γ, ρ' (φ.rangeRestrict g) = ρ g := fun g => rfl

  let P₁ : Subgroup Δ := W.map φ.rangeRestrict
  haveI : P₁.Normal := Subgroup.Normal.map hWn _ φ.rangeRestrict_surjective
  have hP₁ : IsPGroup p P₁ := by
    intro x
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨a, ha⟩ := hW w hw
    refine ⟨a, Subtype.ext ?_⟩
    show (x : Δ) ^ p ^ a = 1
    rw [← hwx, ← map_pow]
    apply Subtype.ext
    apply Units.ext
    show ((φ (w ^ p ^ a) : (V →ₗ[k] V)ˣ) : V →ₗ[k] V) = 1
    exact ha
  have hsimple' : ∀ W' : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W' → ρ' d v ∈ W') → W' = ⊥ ∨ W' = ⊤ := by
    intro W' hW'
    exact hsimple W' (fun g v hv => by rw [← hρ']; exact hW' _ v hv)
  have hfr : Module.finrank k V ≠ 0 := Module.finrank_pos.ne'
  have key := Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple ρ' hfr hsimple' P₁ hP₁

  have hWtriv : ∀ w ∈ W, ρ w = 1 := by
    intro w hw
    rw [← hρ']
    exact key _ (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
  exact comm_of_commutator_ker ρ (fun g h => hWtriv _ (hcommW g h))

end Unipotent

section FieldPart

variable {R₀ : Type u₁} [CommRing R₀] {H : Type u₂} [CommRing H] [HopfAlgebra R₀ H]
  [Coalgebra.IsCocomm R₀ H] {L : Type u₃} [Field L] [Algebra R₀ L] {p : ℕ}
  [hp : Fact p.Prime] [hM : Fact (∀ f : WithConv (H →ₐ[R₀] L), f ^ p = 1)]
  (K K' : Submonoid (Pt R₀ H L p))
  {Γ : Type*} [Group Γ] (τ : Γ →* (L →ₐ[R₀] L))
  (hK : ∀ γ : Γ, ∀ f ∈ K, postComp (p := p) (τ γ) f ∈ K)
  (hK' : ∀ γ : Γ, ∀ f ∈ K', postComp (p := p) (τ γ) f ∈ K')
  (hKK' : K ≤ K')
  (hstep : ∀ S : Submonoid (Pt R₀ H L p), K ≤ S → S ≤ K' →
      (∀ γ : Γ, ∀ f ∈ S, postComp (p := p) (τ γ) f ∈ S) → S = K ∨ S = K')
  (hcomm : ∀ γ γ' : Γ, rep K K' τ hK hK' γ * rep K K' τ hK hK' γ' = rep K K' τ hK hK' γ' * rep K K' τ hK hK' γ)

theorem ofMul_cls_ne_zero {f : Pt R₀ H L p} (hf : f ∈ K') (hfK : f ∉ K) :
    Additive.ofMul (cls K K' f hf) ≠ 0 := by
  intro h
  apply hfK
  rw [← cls_eq_one_iff K K' hf]
  exact Additive.ofMul.injective h

include hKK' hstep hcomm in

theorem isField_and_bijective {f₀ : Pt R₀ H L p} (hf₀ : f₀ ∈ K') (hf₀K : f₀ ∉ K) :
    IsField (Comm K K' τ hK hK') ∧
      ∀ v : Additive (V K K'), v ≠ 0 →
        Function.Bijective (fun a : Comm K K' τ hK hK' => (a : Module.End (ZMod p) (Additive (V K K'))) v) := by
  haveI : Nontrivial (Additive (V K K')) :=
    ⟨⟨Additive.ofMul (cls K K' f₀ hf₀), 0, ofMul_cls_ne_zero K K' hf₀ hf₀K⟩⟩
  obtain ⟨-, hF, hbij⟩ :=
    Representation.centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute (rep K K' τ hK hK')
      (fun W hW => rep_simple K K' τ hK hK' hKK' hstep W hW) hcomm
  exact ⟨hF, hbij⟩

include hKK' hstep hcomm in
theorem line {f₀ : Pt R₀ H L p} (hf₀ : f₀ ∈ K') (hf₀K : f₀ ∉ K) (g : Pt R₀ H L p) (hg : g ∈ K') :
    ∃ a : Comm K K' τ hK hK', ∃ k ∈ K, g = act K K' τ hK hK' a f₀ * k := by
  obtain ⟨-, hbij⟩ := isField_and_bijective K K' τ hK hK' hKK' hstep hcomm hf₀ hf₀K
  obtain ⟨a, ha⟩ := (hbij _ (ofMul_cls_ne_zero K K' hf₀ hf₀K)).2 (Additive.ofMul (cls K K' g hg))
  refine ⟨a, exists_mul_of_cls_eq K K' (act_mem K K' τ hK hK' a f₀ hf₀) hg ?_⟩
  rw [ofMul_cls_act]
  exact ha

include hKK' hstep hcomm in
theorem free {f₀ : Pt R₀ H L p} (hf₀ : f₀ ∈ K') (hf₀K : f₀ ∉ K) (a b : Comm K K' τ hK hK')
    (h : ∃ k ∈ K, act K K' τ hK hK' a f₀ = act K K' τ hK hK' b f₀ * k) : a = b := by
  obtain ⟨-, hbij⟩ := isField_and_bijective K K' τ hK hK' hKK' hstep hcomm hf₀ hf₀K
  apply (hbij _ (ofMul_cls_ne_zero K K' hf₀ hf₀K)).1
  simp only []
  rw [← ofMul_cls_act K K' τ hK hK' a f₀ hf₀, ← ofMul_cls_act K K' τ hK hK' b f₀ hf₀]
  congr 1
  exact ((cls_eq_cls_iff K K' (act_mem K K' τ hK hK' b f₀ hf₀) (act_mem K K' τ hK hK' a f₀ hf₀)).mpr h).symm

include hKK' hstep hcomm in

theorem natCard_comm [Finite (V K K')] {f₀ : Pt R₀ H L p} (hf₀ : f₀ ∈ K') (hf₀K : f₀ ∉ K) :
    Nat.card (Comm K K' τ hK hK') = Nat.card (V K K') := by
  obtain ⟨-, hbij⟩ := isField_and_bijective K K' τ hK hK' hKK' hstep hcomm hf₀ hf₀K
  have := Nat.card_eq_of_bijective _ (hbij _ (ofMul_cls_ne_zero K K' hf₀ hf₀K))
  rw [this]
  rfl

include hKK' hstep hcomm in
theorem finite_comm [Finite (V K K')] {f₀ : Pt R₀ H L p} (hf₀ : f₀ ∈ K') (hf₀K : f₀ ∉ K) :
    Finite (Comm K K' τ hK hK') := by
  obtain ⟨-, hbij⟩ := isField_and_bijective K K' τ hK hK' hKK' hstep hcomm hf₀ hf₀K
  exact Finite.of_injective _ (hbij _ (ofMul_cls_ne_zero K K' hf₀ hf₀K)).1

end FieldPart

end StepLineE72
p2m_reactivate "P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step.StepLineE72"

section Assembly

open StepLineE72

theorem finite_points_D0 {p : ℕ} (hp : p.Prime)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H] :
    Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) := by
  haveI := GaloisRep.ratLocalizedAt.isLocalRing hp
  haveI : Module.Free (GaloisRep.ratLocalizedAt p) H := Module.free_of_flat_of_isLocalRing
  have hcard := HopfAlgebra.natCard_algHom_eq_finrank_of_charZero (GaloisRep.ratLocalizedAt p) H
    (AlgebraicClosure ℚ)
  haveI : Nontrivial H := ⟨⟨0, 1, fun h => zero_ne_one (α := ↥(GaloisRep.ratLocalizedAt p))
    (by simpa using congrArg (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) h)⟩⟩
  have hpos : 0 < Module.finrank (GaloisRep.ratLocalizedAt p) H :=
    (Module.finrank_pos_iff_of_free (GaloisRep.ratLocalizedAt p) H).mpr inferInstance
  have e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
    ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩
  have : Nat.card (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) =
      Module.finrank (GaloisRep.ratLocalizedAt p) H := by rw [← hcard]; exact Nat.card_congr e
  exact Nat.finite_of_card_ne_zero (by omega)

theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) [NeZero s] (hcard : Nat.card K' = p ^ s * Nat.card K) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (act : F → WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →
        WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      Fintype.card F = p ^ s ∧
      (∀ a : F, ∀ f ∈ K', act a f ∈ K') ∧
      (∀ a : F, ∀ f ∈ K', ∀ k ∈ K, ∃ k' ∈ K, act a (f * k) = act a f * k') ∧
      (∀ a : F, ∀ f ∈ K', ∀ g ∈ K', ∃ k ∈ K, act a (f * g) = act a f * act a g * k) ∧
      (∀ a b : F, ∀ f ∈ K', ∃ k ∈ K, act (a + b) f = act a f * act b f * k) ∧
      (∀ a b : F, ∀ f ∈ K', ∃ k ∈ K, act (a * b) f = act a (act b f) * k) ∧
      (∀ f ∈ K', ∃ k ∈ K, act 1 f = f * k) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : F, ∀ f ∈ K',
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → ∃ k ∈ K, ∀ h : H, (act a g * k) h = σ ((act a f) h)) ∧
      (∀ f₀ ∈ K', f₀ ∉ K → ∀ g ∈ K', ∃ a : F, ∃ k ∈ K, g = act a f₀ * k) ∧
      (∀ f₀ ∈ K', f₀ ∉ K → ∀ a b : F, (∃ k ∈ K, act a f₀ = act b f₀ * k) → a = b) := by
  classical
  haveI hpF : Fact p.Prime := ⟨hp⟩
  haveI : Fact (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1) := ⟨hMp⟩
  haveI hfin := finite_points_D0 hp (H := H)

  let Γ := ↥(P.inertiaSubgroupIn ℚ)
  let τ : Γ →* (AlgebraicClosure ℚ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
    { toFun := fun σ => ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars (GaloisRep.ratLocalizedAt p)
      map_one' := by apply AlgHom.ext; intro x; rfl
      map_mul' := fun _ _ => by apply AlgHom.ext; intro x; rfl }
  have hτ : ∀ (γ : Γ) (x : AlgebraicClosure ℚ), τ γ x = (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x :=
    fun _ _ => rfl

  let Kp : Submonoid (Pt (GaloisRep.ratLocalizedAt p) H (AlgebraicClosure ℚ) p) := K
  let Kp' : Submonoid (Pt (GaloisRep.ratLocalizedAt p) H (AlgebraicClosure ℚ) p) := K'
  have hpc : ∀ (γ : Γ) (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (h : H),
      (ofPt (postComp (p := p) (τ γ) f) : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) h =
        (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f h) :=
    fun _ _ _ => rfl
  have hKγ : ∀ γ : Γ, ∀ f ∈ Kp, postComp (p := p) (τ γ) f ∈ Kp :=
    fun γ f hf => hK γ.1 γ.2 f hf _ (hpc γ f)
  have hK'γ : ∀ γ : Γ, ∀ f ∈ Kp', postComp (p := p) (τ γ) f ∈ Kp' :=
    fun γ f hf => hK' γ.1 γ.2 f hf _ (hpc γ f)
  have hstepγ : ∀ S : Submonoid (Pt (GaloisRep.ratLocalizedAt p) H (AlgebraicClosure ℚ) p),
      Kp ≤ S → S ≤ Kp' → (∀ γ : Γ, ∀ f ∈ S, postComp (p := p) (τ γ) f ∈ S) → S = Kp ∨ S = Kp' := by
    intro S h1 h2 h3
    refine hstep S h1 h2 (fun σ hσ f hf g hg => ?_)
    have : g = postComp (p := p) (τ ⟨σ, hσ⟩) f := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro h
      exact hg h
    rw [this]
    exact h3 ⟨σ, hσ⟩ f hf

  haveI hfinPt : Finite (Pt (GaloisRep.ratLocalizedAt p) H (AlgebraicClosure ℚ) p) := hfin
  have hfinK : Finite K := Finite.of_injective _ Subtype.val_injective
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hne : ∃ f₀ ∈ K', f₀ ∉ K := by
    by_contra hall
    push Not at hall
    have hKK : K' = K := le_antisymm (fun f hf => hall f hf) hKK'
    rw [hKK] at hcard
    have : p ^ s = 1 := by
      have := hcard; nlinarith [Nat.one_le_pow s p hp.pos]
    have h2 : 2 ≤ p ^ s := le_trans hp.two_le (Nat.le_self_pow (NeZero.ne s) p)
    omega
  obtain ⟨f₀, hf₀, hf₀K⟩ := hne
  haveI : Finite (V Kp Kp') := inferInstance
  haveI : Nontrivial (Additive (V Kp Kp')) :=
    ⟨⟨Additive.ofMul (cls Kp Kp' f₀ hf₀), 0, ofMul_cls_ne_zero Kp Kp' hf₀ hf₀K⟩⟩

  let Wsub : Subgroup Γ :=
    { carrier := {σ | WildE72.IsWild P σ.1}
      one_mem' := by
        show WildE72.IsWild P (1 : Γ).1
        rw [WildE72.isWild_iff_resHom]; intro z hz; exact map_one _
      mul_mem' := by
        intro a b ha hb
        have ha' := (WildE72.isWild_iff_resHom P a).mp ha
        have hb' := (WildE72.isWild_iff_resHom P b).mp hb
        show WildE72.IsWild P (a * b).1
        rw [WildE72.isWild_iff_resHom]; intro z hz; rw [map_mul, ha' z hz, hb' z hz, one_mul]
      inv_mem' := by
        intro a ha
        have ha' := (WildE72.isWild_iff_resHom P a).mp ha
        show WildE72.IsWild P (a⁻¹).1
        rw [WildE72.isWild_iff_resHom]; intro z hz; rw [WildE72.resHom_inv, ha' z hz, inv_one] }
  haveI : Wsub.Normal := ⟨fun a ha g => by
    have ha' := (WildE72.isWild_iff_resHom P a).mp ha
    show WildE72.IsWild P (g * a * g⁻¹).1
    rw [WildE72.isWild_iff_resHom]; intro z hz
    rw [map_mul, map_mul, WildE72.resHom_inv, ha' z hz, mul_one, mul_inv_cancel₀ (WildE72.resHom_ne_zero P z hz g)]⟩
  have hWpow : ∀ w ∈ Wsub, ∃ a : ℕ, rep Kp Kp' τ hKγ hK'γ (w ^ (p ^ a)) = 1 := by
    intro w hw
    obtain ⟨a, ha⟩ := WildE72.exists_pow_fixes_points hp (H := H) P hP (σ := w.1) hw
    refine ⟨a, ?_⟩
    apply LinearMap.ext
    intro v
    obtain ⟨f, hf, rfl⟩ := exists_eq_ofMul_cls Kp Kp' v
    rw [rep_apply_ofMul_cls]
    show Additive.ofMul _ = Additive.ofMul _
    congr 1
    exact cls_congr Kp Kp' _ _ (by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro h
      exact ha f h)
  have hWcomm : ∀ g h : Γ, g * h * g⁻¹ * h⁻¹ ∈ Wsub := fun g h => WildE72.isWild_commutator P g h
  have hcomm : ∀ γ γ' : Γ, rep Kp Kp' τ hKγ hK'γ γ * rep Kp Kp' τ hKγ hK'γ γ' =
      rep Kp Kp' τ hKγ hK'γ γ' * rep Kp Kp' τ hKγ hK'γ γ :=
    rep_comm_of_normal_unipotent (rep Kp Kp' τ hKγ hK'γ)
      (fun W hW => rep_simple Kp Kp' τ hKγ hK'γ hKK' hstepγ W hW) Wsub hWpow hWcomm

  obtain ⟨hF, hbij⟩ := isField_and_bijective Kp Kp' τ hKγ hK'γ hKK' hstepγ hcomm hf₀ hf₀K
  haveI hFin := finite_comm Kp Kp' τ hKγ hK'γ hKK' hstepγ hcomm hf₀ hf₀K
  letI : Field (Comm Kp Kp' τ hKγ hK'γ) := hF.toField
  letI : Fintype (Comm Kp Kp' τ hKγ hK'γ) := Fintype.ofFinite _
  refine ⟨Comm Kp Kp' τ hKγ hK'γ, inferInstance, inferInstance, act Kp Kp' τ hKγ hK'γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Fintype.card_eq_nat_card, natCard_comm Kp Kp' τ hKγ hK'γ hKK' hstepγ hcomm hf₀ hf₀K]
    have h := card_V_mul Kp Kp' hKK'
    rw [show (Nat.card Kp' : ℕ) = Nat.card K' from rfl, show (Nat.card Kp : ℕ) = Nat.card K from rfl, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hKpos h
  · exact fun a f hf => act_mem Kp Kp' τ hKγ hK'γ a f hf
  · exact fun a f hf k hk => act_descends Kp Kp' τ hKγ hK'γ hKK' a f hf k hk
  · exact fun a f hf g hg => act_mul_pt Kp Kp' τ hKγ hK'γ a f g hf hg
  · exact fun a b f hf => act_add Kp Kp' τ hKγ hK'γ a b f hf
  · exact fun a b f hf => act_mul Kp Kp' τ hKγ hK'γ a b f hf
  · exact fun f hf => act_one Kp Kp' τ hKγ hK'γ f hf
  · intro σ hσ a f hf g hg
    have hgf : g = postComp (p := p) (τ ⟨σ, hσ⟩) f := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro h
      exact hg h
    obtain ⟨k, hk, hk'⟩ := act_equivariant Kp Kp' τ hKγ hK'γ a ⟨σ, hσ⟩ f hf
    refine ⟨k, hk, fun h => ?_⟩
    have e1 := congrArg (fun x : Pt (GaloisRep.ratLocalizedAt p) H (AlgebraicClosure ℚ) p =>
      (ofPt x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) h) hk'
    rw [hgf]
    exact e1.symm
  · exact fun f₀ hf₀ hf₀K g hg => line Kp Kp' τ hKγ hK'γ hKK' hstepγ hcomm hf₀ hf₀K g hg
  · exact fun f₀ hf₀ hf₀K a b h => free Kp Kp' τ hKγ hK'γ hKK' hstepγ hcomm hf₀ hf₀K a b h

end Assembly
p2m_reactivate "P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step.StepLineE72"

end
end S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
end P2MW
export P2MW.S_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step (solution)
