-- Prove2me | solution 1 for LT.HeckeChar.exists_heckeCharOfRayClassChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2eaf462d-928c-5dd9-b77c-f6dd51e6f2d5

import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar

set_option autoImplicit false
set_option Elab.async false

section Fold_FadContent

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "IsFiniteOrderHeckeChar idealMultiplicity AdmitsModulus"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageA

theorem fad_one_apply (v : HeightOneSpectrum (𝓞 K)) :
    ((1 : FiniteAdeleRing (𝓞 K) K) v : v.adicCompletion K) = 1 := rfl

theorem fad_mul_apply (a b : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ((a * b : FiniteAdeleRing (𝓞 K) K) v : v.adicCompletion K) = a v * b v := rfl

def placeOrd (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  -WithZero.log (Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v))

theorem placeOrd_one (v : HeightOneSpectrum (𝓞 K)) : placeOrd K 1 v = 0 := by
  unfold placeOrd
  rw [Units.val_one, fad_one_apply, map_one, WithZero.log_one, neg_zero]

theorem valued_ne_zero_of_unit (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  exact ((FiniteAdeleRing.isUnit_iff.mp u.isUnit).1 v)

theorem placeOrd_mul (u u' : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (u * u') v = placeOrd K u v + placeOrd K u' v := by
  unfold placeOrd
  rw [Units.val_mul, fad_mul_apply, map_mul,
    WithZero.log_mul (valued_ne_zero_of_unit K u v) (valued_ne_zero_of_unit K u' v),
    neg_add]

theorem placeOrd_eq_zero_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K u v = 0 ↔ Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  unfold placeOrd
  rw [neg_eq_zero]
  constructor
  · intro hlog
    have h := WithZero.exp_log (x := Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v))
      (valued_ne_zero_of_unit K u v)
    rw [hlog, WithZero.exp_zero] at h
    exact h.symm
  · intro h; rw [h, WithZero.log_one]

theorem finite_support_placeOrd (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (Function.support (placeOrd K u)).Finite := by
  have h := FiniteAdeleRing.unitsEquiv_finite_valued_eq_one (R := 𝓞 K) (K := K) u
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  rw [Function.mem_support] at hv
  rw [Set.mem_setOf_eq]
  intro hval
  exact hv ((placeOrd_eq_zero_iff K u v).mpr (by
    simp [RestrictedProduct.unitsEquiv_apply] at hval
    exact hval))

def fadContentHom : (FiniteAdeleRing (𝓞 K) K)ˣ →* (FractionalIdeal ((𝓞 K)⁰) K)ˣ where
  toFun u := ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v)
  map_one' := by simp [placeOrd_one]
  map_mul' u u' := by
    simp only [placeOrd_mul, zpow_add]
    exact finprod_mul_distrib
      ((finite_support_placeOrd K u).subset fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
        contrapose! hv; rw [Function.mem_support, not_not] at hv; simp [hv])
      ((finite_support_placeOrd K u').subset fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
        contrapose! hv; rw [Function.mem_support, not_not] at hv; simp [hv])

theorem fadContentHom_apply (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v) :=
  rfl

theorem fadContentHom_single_uniformizer (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    {v : HeightOneSpectrum (𝓞 K)}
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : FiniteAdeleRing (𝓞 K) K) w) = 1)
    (huv : Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = WithZero.exp (-1 : ℤ)) :
    fadContentHom K u = primeUnit K v := by
  rw [fadContentHom_apply]
  rw [finprod_eq_single _ v]
  · have : placeOrd K u v = 1 := by unfold placeOrd; rw [huv, WithZero.log_exp]; ring
    rw [this, zpow_one]
  · intro w hwv
    have : placeOrd K u w = 0 := (placeOrd_eq_zero_iff K u w).mpr (huw w hwv)
    rw [this, zpow_zero]

end StageA

section StageB

theorem coe_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (placeOrd K u v) := by
  rw [fadContentHom_apply, ← Units.coeHom_apply,
    (Units.coeHom _).map_finprod_of_preimage_one (fun _ h => Units.ext h)
      (fun v => primeUnit K v ^ placeOrd K u v)]
  refine finprod_congr fun v => ?_
  rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, primeUnit_val]

theorem count_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = placeOrd K u w := by
  rw [coe_fadContentHom]
  exact FractionalIdeal.count_finprod K w (placeOrd K u) (by
    rw [Filter.eventually_cofinite]
    exact finite_support_placeOrd K u)

theorem fadContentHom_mem_coprimeToModulus_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (𝔣 : Ideal (𝓞 K)) :
    fadContentHom K u ∈ coprimeToModulus K 𝔣 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  rw [mem_coprimeToModulus_iff]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [count_fadContentHom, placeOrd_eq_zero_iff]

theorem placeOrd_unitEmbedding (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K)) := by
  classical

  have hLHS : placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = -WithZero.log (v.valuation K (α : K)) := by
    unfold placeOrd
    rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
      FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (α : K)]
  rw [hLHS]

  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (M := (𝓞 K)⁰) (S := K) (α : K)
  have hnd' : IsLocalization.mk' K n d = (α : K) := hnd
  have hn0 : n ≠ 0 := by
    rintro rfl; simp only [IsLocalization.mk'_zero] at hnd'; exact α.ne_zero hnd'.symm
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  rw [← hnd', HeightOneSpectrum.valuation_of_mk',
    HeightOneSpectrum.intValuation_if_neg _ hn0, HeightOneSpectrum.intValuation_if_neg _ hd0,
    ← WithZero.exp_sub, WithZero.log_exp, neg_sub_neg,
    IsFractionRing.mk'_eq_div, div_eq_mul_inv,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0)
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, inv_eq_zero]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0),
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn0),
    show FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d)⁻¹
        = (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d))⁻¹ by
        rw [← one_div, ← FractionalIdeal.spanSingleton_div_spanSingleton,
          FractionalIdeal.spanSingleton_one, one_div],
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd0)]
  ring

theorem coe_fadContentHom_principal (α : Kˣ) :
    ((fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K) := by
  rw [coe_fadContentHom]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K))
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr α.ne_zero)]
  exact finprod_congr fun v => by rw [placeOrd_unitEmbedding]

theorem fadContentHom_unitEmbedding (α : Kˣ) :
    fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) = toPrincipalIdeal (𝓞 K) K α :=
  Units.ext <| (coe_fadContentHom_principal K α).trans (coe_toPrincipalIdeal α).symm

end StageB

end HeckeCharacter

end

end Fold_FadContent

section Fold_IdeleContentBuild

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "IsFiniteOrderHeckeChar idealMultiplicity AdmitsModulus"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageC

def projFin : (AdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (MonoidHom.snd (InfiniteAdeleRing K)ˣ (FiniteAdeleRing (𝓞 K) K)ˣ).comp
    MulEquiv.prodUnits.toMonoidHom

theorem projFin_val (u : (AdeleRing (𝓞 K) K)ˣ) :
    ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) =
      (u : AdeleRing (𝓞 K) K).2 := rfl

theorem projFin_principal (α : Kˣ) :
    projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)
      = FiniteAdeleRing.unitEmbedding (𝓞 K) K α := by
  apply Units.ext; rfl

noncomputable def placeOf (τ : K →+* ℝ) : InfinitePlace K :=
  InfinitePlace.mk (Complex.ofRealHom.comp τ)

omit [NumberField K] in

theorem isReal_compOfRealHom (τ : K →+* ℝ) :
    ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
  RingHom.ext fun x => Complex.conj_ofReal (τ x)

omit [NumberField K] in
theorem isReal_placeOf (τ : K →+* ℝ) : (placeOf K τ).IsReal :=
  ⟨_, isReal_compOfRealHom K τ, rfl⟩

open _root_.NumberField.InfinitePlace.Completion in

noncomputable def archRealProjTau (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) : ℝ :=
  ringEquivRealOfIsReal (isReal_placeOf K τ)
    (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) (placeOf K τ))

open _root_.NumberField.InfinitePlace.Completion in
theorem archRealProjTau_mul (τ : K →+* ℝ) (u u' : (AdeleRing (𝓞 K) K)ˣ) :
    archRealProjTau K τ (u * u') = archRealProjTau K τ u * archRealProjTau K τ u' := by
  unfold archRealProjTau
  rw [← map_mul]; rfl

open _root_.NumberField.InfinitePlace.Completion in
theorem archRealProjTau_ne_zero (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archRealProjTau K τ u ≠ 0 := by
  intro h
  have h1 : archRealProjTau K τ u * archRealProjTau K τ u⁻¹ = 1 := by
    rw [← archRealProjTau_mul, mul_inv_cancel]
    unfold archRealProjTau; rw [Units.val_one]
    exact (congrArg (ringEquivRealOfIsReal (isReal_placeOf K τ)) rfl).trans (map_one _)
  rw [h, zero_mul] at h1; exact zero_ne_one h1

def archSign (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) : Prop :=
  0 < archRealProjTau K τ u

open _root_.NumberField.InfinitePlace.Completion in

theorem archSign_of_fst_eq_one (τ : K →+* ℝ) {u : (AdeleRing (𝓞 K) K)ˣ}
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1) : archSign K τ u := by
  show (0:ℝ) < ringEquivRealOfIsReal (isReal_placeOf K τ) _
  rw [huarch, show ((1 : InfiniteAdeleRing K) (placeOf K τ)) = 1 from rfl, map_one]
  exact one_pos

omit [NumberField K] in

theorem embedding_of_isReal_placeOf (τ : K →+* ℝ) :
    InfinitePlace.embedding_of_isReal (isReal_placeOf K τ) = τ := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, show (placeOf K τ).embedding
      = Complex.ofRealHom.comp τ from
    InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

theorem archSign_principal (τ : K →+* ℝ) (α : Kˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) ↔ 0 < τ (α : K) := by
  unfold archSign archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe,
    embedding_of_isReal_placeOf K τ]
  rfl

theorem archSign_mul (τ : K →+* ℝ) (u u' : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ (u * u') ↔ (archSign K τ u ↔ archSign K τ u') := by
  unfold archSign; rw [archRealProjTau_mul]
  constructor
  · intro hmul
    rcases mul_pos_iff.mp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact iff_of_true h1 h2
    · exact iff_of_false h1.not_gt h2.not_gt
  · intro hiff
    rcases (archRealProjTau_ne_zero K τ u).lt_or_gt with h1 | h1
    · have h2 := (not_iff_not.mpr hiff).mp h1.not_gt
      exact mul_pos_of_neg_of_neg h1 ((archRealProjTau_ne_zero K τ u').lt_or_gt.resolve_right h2)
    · exact mul_pos h1 (hiff.mp h1)

theorem archSign_one (τ : K →+* ℝ) : archSign K τ 1 :=
  archSign_of_fst_eq_one K τ rfl

theorem archSign_inv (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ u⁻¹ ↔ archSign K τ u := by
  have h := archSign_mul K τ u u⁻¹
  rw [mul_inv_cancel, iff_true_intro (archSign_one K τ), true_iff] at h
  exact h.symm

structure IsAdjuster (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) : Prop where
  cong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
    Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
    Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1)
      ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))
  sign : ∀ τ : K →+* ℝ,
    archSign K τ (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)

theorem IsAdjuster.coprime {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ}
    (h : IsAdjuster K 𝔣 u α) :
    fadContentHom K (projFin K (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹))
      ∈ coprimeToModulus K 𝔣 := by
  rw [fadContentHom_mem_coprimeToModulus_iff]
  intro v hv
  rw [projFin_val]
  exact (h.cong v hv).1

theorem isAdjuster_one_one (𝔣 : Ideal (𝓞 K)) : IsAdjuster K 𝔣 1 1 := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · simp only [map_one, inv_one, mul_one]
    refine ⟨?_, ?_⟩
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
      rw [fad_one_apply]; exact map_one _
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
      rw [fad_one_apply, sub_self, map_zero]; exact zero_le'
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one K τ rfl

theorem unit_cong_mul {v : HeightOneSpectrum (𝓞 K)} {ε : ℤᵐ⁰} {a b : v.adicCompletion K}
    (hva : Valued.v a = 1) (hca : Valued.v (a - 1) ≤ ε)
    (hvb : Valued.v b = 1) (hcb : Valued.v (b - 1) ≤ ε) :
    Valued.v (a * b) = 1 ∧ Valued.v (a * b - 1) ≤ ε := by
  refine ⟨by rw [map_mul, hva, hvb, one_mul], ?_⟩
  have heq : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  calc Valued.v (a * b - 1) = Valued.v (a * (b - 1) + (a - 1)) := by rw [heq]
    _ ≤ max (Valued.v (a * (b - 1))) (Valued.v (a - 1)) := Valuation.map_add _ _ _
    _ ≤ ε := by
        rw [map_mul, hva, one_mul]
        exact max_le hcb hca

private abbrev adjFinV (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem four_comm {G : Type*} [CommMonoid G] (a b c d : G) :
    a * b * (d * c) = a * c * (b * d) := by
  simp only [mul_comm, mul_left_comm]

private abbrev pK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K))

private theorem adj_adele_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    u * u' * (pK K (α * α'))⁻¹ = (u * (pK K α)⁻¹) * (u' * (pK K α')⁻¹) := by
  rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _

private theorem adj_adele_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    (u * (pK K α)⁻¹)⁻¹ * (u * (pK K α')⁻¹) = pK K (α * α'⁻¹) := by
  rw [mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc, ← mul_assoc u⁻¹, inv_mul_cancel,
    one_mul]

private theorem adjFinV_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    adjFinV K (u * u') (α * α') v = adjFinV K u α v * adjFinV K u' α' v := by
  unfold adjFinV
  rw [show u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) from by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _]
  exact fad_mul_apply K _ _ v

theorem IsAdjuster.mul {𝔣 : Ideal (𝓞 K)} {u u' : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u' α') :
    IsAdjuster K 𝔣 (u * u') (α * α') := by
  have hfac : u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) := by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _
  refine ⟨fun v hv𝔣 => ?_, fun τ => ?_⟩
  · show Valued.v (adjFinV K (u * u') (α * α') v) = 1 ∧
      Valued.v (adjFinV K (u * u') (α * α') v - 1) ≤ _
    rw [adjFinV_mul]
    exact unit_cong_mul K (hα.cong v hv𝔣).1 (hα.cong v hv𝔣).2 (hα'.cong v hv𝔣).1
      (hα'.cong v hv𝔣).2
  · rw [hfac, archSign_mul K τ]
    exact iff_of_true (hα.sign τ) (hα'.sign τ)

theorem isAdjuster_principal_self (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    IsAdjuster K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · have h1 : adjFinV K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α v = 1 := by
      unfold adjFinV; simp only [mul_inv_cancel, Units.val_one]
      exact fad_one_apply K v
    show Valued.v (adjFinV K _ α v) = 1 ∧ Valued.v (adjFinV K _ α v - 1) ≤ _
    rw [h1]
    exact ⟨map_one _, by rw [sub_self, map_zero]; exact zero_le'⟩
  · have h1 : (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α : (AdeleRing (𝓞 K) K)ˣ)
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ = 1 := mul_inv_cancel _
    rw [h1]; exact archSign_one K τ

theorem unit_cong_div {v : HeightOneSpectrum (𝓞 K)} {ε : ℤᵐ⁰} {a b : v.adicCompletion K}
    (hca : Valued.v (a - 1) ≤ ε)
    (hvb : Valued.v b = 1) (hcb : Valued.v (b - 1) ≤ ε) :
    Valued.v (a * b⁻¹ - 1) ≤ ε := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hvb
  have heq : a * b⁻¹ - 1 = (a - b) * b⁻¹ := by field_simp
  rw [heq, map_mul, map_inv₀, hvb, inv_one, mul_one]
  calc Valued.v (a - b) = Valued.v ((a - 1) - (b - 1)) := by ring_nf
    _ ≤ max (Valued.v (a - 1)) (Valued.v (b - 1)) := Valuation.map_sub _ _ _
    _ ≤ ε := max_le hca hcb

theorem fad_units_inv_apply (X : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (((X⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)
      = (((X : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← fad_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, fad_one_apply]

theorem adjFinV_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K)
      = adjFinV K u α' v * (adjFinV K u α v)⁻¹ := by
  have hkey := congrArg (fun x : (FiniteAdeleRing (𝓞 K) K)ˣ =>
    ((x : FiniteAdeleRing (𝓞 K) K) : FiniteAdeleRing (𝓞 K) K) v)
    (congrArg (projFin K) (adj_adele_ratio K u α α'))
  rw [map_mul, map_inv, projFin_principal] at hkey
  simp only [Units.val_mul, fad_mul_apply, fad_units_inv_apply, projFin_val] at hkey
  rw [show ((FiniteAdeleRing.unitEmbedding (𝓞 K) K (α * α'⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) from by
    rw [FiniteAdeleRing.unitEmbedding_apply]; exact FiniteAdeleRing.algebraMap_apply ..] at hkey
  rw [← hkey, mul_comm]; rfl

theorem valuation_ratio_sub_one_le {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α')
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K (((α * α'⁻¹ : Kˣ) : K) - 1)
      ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
  rw [← v.valuedAdicCompletion_eq_valuation']
  have hcoe : ((((α * α'⁻¹ : Kˣ) : K) - 1 : K) : v.adicCompletion K)
      = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) - 1 := by
    apply (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv (K := K) (v := v)).injective
    simp [map_sub, map_one, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_one]
  rw [hcoe, adjFinV_ratio K u α α']
  exact unit_cong_div K (hα'.cong v hv).2 (hα.cong v hv).1 (hα.cong v hv).2

theorem ratio_totally_positive {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') (τ : K →+* ℝ) :
    0 < τ ((α * α'⁻¹ : Kˣ) : K) := by
  rw [← archSign_principal K τ, show Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'⁻¹)
    = pK K (α * α'⁻¹) from rfl, map_mul, map_inv, archSign_mul K τ, archSign_inv K τ]
  have h1 : archSign K τ u ↔ archSign K τ (pK K α) := by
    have := hα.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  have h2 : archSign K τ u ↔ archSign K τ (pK K α') := by
    have := hα'.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  exact h1.symm.trans h2

theorem valuation_eq_one_of_cong {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {β : K}
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (β - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K β = 1 := by
  have hm1 : 1 ≤ idealMultiplicity K v 𝔣 := by
    unfold idealMultiplicity
    rwa [Nat.one_le_iff_ne_zero, Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible]
  have hlt : v.valuation K (β - 1) < 1 :=
    lt_of_le_of_lt (hcong v hv) (by
      rw [show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
        WithZero.exp_lt_exp]
      omega)
  have hβ : β = (β - 1) + 1 := (sub_add_cancel β 1).symm
  rw [hβ, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

theorem count_spanSingleton_eq_zero_of_valuation_eq_one {β : Kˣ}
    (v : HeightOneSpectrum (𝓞 K)) (h : v.valuation K (β : K) = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 := by
  rw [← placeOrd_unitEmbedding]
  unfold placeOrd
  rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
    FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (β : K), h,
    WithZero.log_one, neg_zero]

theorem mem_modulus_of_forall_valuation_le {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {x : 𝓞 K}
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (algebraMap (𝓞 K) K x) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    x ∈ 𝔣 := by
  have h𝔣0 : (𝔣 : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [← Ideal.iInf_maxPowDividing_eq h𝔣0, Submodule.mem_iInf]
  intro v
  show x ∈ v.asIdeal ^ (idealMultiplicity K v 𝔣)
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := K)]
    exact hx v hv
  · have hm0 : idealMultiplicity K v 𝔣 = 0 := by
      unfold idealMultiplicity
      by_contra hne
      exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp hne)
    simp [hm0]

theorem toPrincipalIdeal_mem_narrowRaySubgroup {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (β : Kˣ)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (hsign : ∀ τ : K →+* ℝ, 0 < τ (β : K)) :
    toPrincipalIdeal (𝓞 K) K β ∈ narrowRaySubgroup K 𝔣 := by

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 :=
    fun v hv => count_spanSingleton_eq_zero_of_valuation_eq_one K v
      (valuation_eq_one_of_cong K h𝔣 hcong v hv)

  obtain ⟨d, hd0, hd1, n, hn⟩ := movingLemma K h𝔣 (β : K) β.ne_zero hloc

  have hd0' : (algebraMap (𝓞 K) K) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [map_zero] at hn
    exact β.ne_zero ((mul_eq_zero.mp hn.symm).resolve_left hd0')

  have hnd1 : n - d ∈ 𝔣 := by
    refine mem_modulus_of_forall_valuation_le K h𝔣 fun v hv => ?_
    have hval_d : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      rw [v.valuation_of_algebraMap (K := K)]
      refine le_antisymm (v.intValuation_le_one d) ?_
      rw [← not_lt, v.intValuation_lt_one_iff_mem]
      intro hmem
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr
        (show (1 : 𝓞 K) ∈ v.asIdeal from by
          have : (d : 𝓞 K) - (d - 1) ∈ v.asIdeal := sub_mem hmem
            ((Ideal.dvd_iff_le.mp hv) hd1)
          simpa using this))
    have hsplit : (algebraMap (𝓞 K) K) (n - d)
        = algebraMap (𝓞 K) K d * ((β : K) - 1) := by
      rw [map_sub, hn]; ring
    rw [hsplit, map_mul, hval_d, one_mul]
    exact hcong v hv
  have hn1 : n - 1 ∈ 𝔣 := by
    have : n - 1 = (n - d) + (d - 1) := by ring
    rw [this]; exact add_mem hnd1 hd1

  have hn0' : (algebraMap (𝓞 K) K) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0
  have hsgn : ∀ τ : K →+* ℝ, (0 < τ (algebraMap (𝓞 K) K n))
      ↔ (0 < τ (algebraMap (𝓞 K) K d)) := by
    intro τ
    have hτβ : 0 < τ (β : K) := hsign τ
    rw [show (algebraMap (𝓞 K) K) n = (algebraMap (𝓞 K) K) d * (β : K) from hn,
      map_mul]
    refine ⟨fun h => ?_, fun h => mul_pos h hτβ⟩
    exact ((mul_pos_iff.mp h).resolve_right fun ⟨_, hb⟩ => hb.not_gt hτβ).1

  set yn : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K n hn0, principalUnit_mem_coprimeToModulus K hn0 hn1⟩ with hyn_def
  set yd : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K d hd0, principalUnit_mem_coprimeToModulus K hd0 hd1⟩ with hyd_def
  have hyn_val : ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {n} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K n hn0
  have hyd_val : ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K d hd0

  have hyd2 : ((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hd0 hd1 hyd_val hd0 hd1 hyd_val
      fun _ => Iff.rfl)
  have hynyd : ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hn0 hn1 hyn_val hd0 hd1 hyd_val
      hsgn)

  have hβnd' : toPrincipalIdeal (𝓞 K) K β * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    refine Units.ext ?_
    rw [Units.val_mul, hyn_val, hyd_val, coe_toPrincipalIdeal,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm, hn]
  have hβnd : toPrincipalIdeal (𝓞 K) K β
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹ :=
    eq_mul_inv_of_mul_eq hβnd'

  rw [hβnd]
  have hrw : (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹
      = (((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
        * ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc,
      show ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
          * ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))
        = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) from by
          rw [mul_comm (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) _, ← mul_assoc, inv_mul_cancel,
            one_mul],
      mul_comm]
  rw [hrw]
  exact mul_mem (inv_mem hyd2) hynyd

theorem mk_eq_mk_of_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') :
    NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩
      = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα'.coprime⟩ := by
  rw [NarrowRayClassGroup.mk_eq_mk_iff]
  show (fadContentHom K (projFin K _))⁻¹ * fadContentHom K (projFin K _) ∈ _
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, adj_adele_ratio K u α α',
    projFin_principal, fadContentHom_unitEmbedding]
  exact toPrincipalIdeal_mem_narrowRaySubgroup K h𝔣 (α * α'⁻¹)
    (fun v hv => valuation_ratio_sub_one_le K hα hα' v hv)
    (fun τ => ratio_totally_positive K hα hα' τ)

end StageC

end HeckeCharacter

end

end Fold_IdeleContentBuild

section Fold_MixedApprox

p2m_open "NumberField P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.NumberField IsDedekindDomain AbsoluteValue"
open Filter Topology

namespace NumberField
p2m_export "NumberField" "FinitePlace InfinitePlace.Completion.extensionEmbeddingOfIsReal FinitePlace.norm_lt_one_iff_mem InfiniteAdeleRing FinitePlace.mk InfinitePlace.embedding_of_isReal_apply AdeleRing.algebraMap_snd_apply InfinitePlace.map_natCast mk InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe place FinitePlace.norm_eq_one_iff_notMem InfinitePlace.embedding_mk_eq_of_isReal FinitePlace.mk_eq_iff InfinitePlace.mk InfinitePlace.denseRange_algebraMap_pi AdeleRing.algebraMap_fst_apply InfinitePlace.Completion FinitePlace.norm_embedding InfinitePlace.embedding_of_isReal HeightOneSpectrum.adicAbv InfinitePlace.eq_iff_isEquiv RingOfIntegers HeightOneSpectrum.adicAbv_def HeightOneSpectrum.adicAbv_natCast_le_one InfinitePlace.apply ComplexEmbedding.IsReal InfinitePlace instNormedFieldValuedAdicCompletion InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal AdeleRing FinitePlace.embedding_apply HeightOneSpectrum.one_lt_absNorm_nnreal InfinitePlace.Completion.ringEquivRealOfIsReal_apply InfinitePlace.isNontrivial InfinitePlace.coe_apply FinitePlace.norm_def FinitePlace.mk_apply FinitePlace.embedding AdelicLevel.idealBound AdelicLevel.idealBound_of_ne_bot AdelicLevel.continuous_archEval AdelicLevel.continuous_adeleArch AdelicLevel.continuous_adeleFin AdelicLevel.integralFiniteAdeles AdelicLevel.idealBall AdelicLevel.idealBall_subset_integralFiniteAdeles AdelicLevel.zero_mem_idealBall AdelicLevel.isOpen_integralFiniteAdeles AdelicLevel.isOpen_idealBall AdelicLevel.one_mem_integralFiniteAdeles AdelicLevel.add_mem_integralFiniteAdeles AdelicLevel.valued_apply_le_one AdelicLevel.localUnit AdelicLevel.localUnit_apply_self AdelicLevel.localUnit_apply_of_ne AdelicLevel.uniformizerUnit AdelicLevel.valued_uniformizerUnit"
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

namespace FinitePlace p2m_export "NumberField.FinitePlace" "norm_lt_one_iff_mem mk coe_apply norm_eq_one_iff_notMem mk_eq_iff pos_iff norm_embedding embedding_apply norm_le_one norm_def mk_apply embedding" end FinitePlace
namespace FinitePlace
p2m_open_scoped "NumberField.FinitePlace" in

private theorem _root_.NumberField.FinitePlace.isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (FinitePlace.mk v).1.IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ v.asIdeal, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr v.ne_bot)
    exact ⟨x, hx, fun h => hx0 (h ▸ Ideal.zero_mem _)⟩
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hx0
  · show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x) ≠ 1
    rw [show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x)
        = ‖FinitePlace.embedding v (algebraMap (𝓞 K) K x)‖ from rfl]
    exact ((FinitePlace.norm_lt_one_iff_mem K v x).mpr hx).ne

end FinitePlace
p2m_export "NumberField" "FinitePlace.isNontrivial"
p2m_open_scoped "NumberField.FinitePlace" in

theorem FinitePlace.not_isEquiv_of_ne {v₁ v₂ : HeightOneSpectrum (𝓞 K)} (h : v₁ ≠ v₂) :
    ¬ (FinitePlace.mk v₁).1.IsEquiv (FinitePlace.mk v₂).1 := by
  rw [isEquiv_iff_lt_one_iff]
  push Not
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h (HeightOneSpectrum.ext_iff.mpr
      (Ideal.IsMaximal.eq_of_le (HeightOneSpectrum.isMaximal v₁) Ideal.IsPrime.ne_top' H))
  refine ⟨algebraMap (𝓞 K) K x, ?_⟩
  rw [show ((FinitePlace.mk v₁).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₁ y‖ from rfl,
    show ((FinitePlace.mk v₂).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₂ y‖ from rfl]
  simp only
  exact Or.inl ⟨(FinitePlace.norm_lt_one_iff_mem K v₁ x).mpr hx1,
    ((FinitePlace.norm_eq_one_iff_notMem K v₂ x).mpr hx2).ge⟩

namespace InfinitePlace p2m_export "NumberField.InfinitePlace" "Completion.extensionEmbeddingOfIsReal embedding_of_isReal_apply IsReal mk_eq_iff Completion.extensionEmbeddingOfIsReal_coe mult embedding_mk_eq_of_isReal mk denseRange_algebraMap_pi Completion embedding_of_isReal eq_iff_isEquiv ext pos_iff apply Completion.isometry_extensionEmbeddingOfIsReal embedding Completion.ringEquivRealOfIsReal_apply isNontrivial coe_apply le_iff_le" end InfinitePlace
p2m_open_scoped "NumberField.InfinitePlace" in

theorem InfinitePlace.not_isEquiv_finitePlace (w : InfinitePlace K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ w.1.IsEquiv (FinitePlace.mk v).1 := by
  intro hequiv
  have hw2 : ¬ w.1 (2 : K) ≤ 1 := by
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [← InfinitePlace.coe_apply, this, InfinitePlace.map_natCast w 2]
    norm_num
  have hv2 : (FinitePlace.mk v).1 (2 : K) ≤ 1 := by
    show ‖FinitePlace.embedding v (2 : K)‖ ≤ 1
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [FinitePlace.norm_embedding, this]
    exact HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  exact hw2 (hequiv.le_one_iff.mpr hv2)

noncomputable def mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ ↥S → AbsoluteValue K ℝ :=
  Sum.elim (·.1) (fun v => (FinitePlace.mk v.1).1)

theorem mixedAbs_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : InfinitePlace K ⊕ ↥S) : (mixedAbs K S i).IsNontrivial := by
  rcases i with w | v
  · exact InfinitePlace.isNontrivial w
  · exact FinitePlace.isNontrivial K v.1

theorem mixedAbs_pairwise_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise fun i j => ¬ (mixedAbs K S i).IsEquiv (mixedAbs K S j) := by
  intro i j hij
  match i, j with
  | Sum.inl w, Sum.inl w' =>
    exact (InfinitePlace.eq_iff_isEquiv (K := K)).not.mp (by simpa using hij)
  | Sum.inl w, Sum.inr v => exact InfinitePlace.not_isEquiv_finitePlace K w v.1
  | Sum.inr v, Sum.inl w =>
    exact fun h => InfinitePlace.not_isEquiv_finitePlace K w v.1 h.symm
  | Sum.inr v, Sum.inr v' =>
    exact FinitePlace.not_isEquiv_of_ne K (by simpa using hij)

theorem denseRange_algebraMap_pi_mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (algebraMap K ((i : InfinitePlace K ⊕ ↥S) → WithAbs (mixedAbs K S i))) := by
  classical
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (mixedAbs_isNontrivial K S) (mixedAbs_pairwise_not_isEquiv K S)
  let y := fun n ↦
    ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (mixedAbs K S i) (z i)
  have htend : Filter.atTop.Tendsto
      (fun n i ↦ (WithAbs.equiv (mixedAbs K S i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have : mixedAbs K S u (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (mixedAbs K S i)) hw (z w)]
      have haw0 : a w ≠ 0 := fun ha => by
        have := (hx w).1; rw [ha, map_zero] at this; linarith
      have hu : 1 < mixedAbs K S u (a w)⁻¹ := by
        rw [map_inv₀, one_lt_inv_iff₀]
        exact ⟨(mixedAbs K S u).pos_iff.2 haw0, (hx w).2 u hw⟩
      have := (mixedAbs K S u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (mixedAbs K S u)).symm (WithAbs.equiv (mixedAbs K S w) (z w)))
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 htend r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

theorem denseRange_algebraMap_pi_mixedAbs_empty :
    DenseRange (algebraMap K ((w : InfinitePlace K) → WithAbs w.1)) :=
  InfinitePlace.denseRange_algebraMap_pi K

end NumberField

end Fold_MixedApprox

section Fold_ExistsAdjuster

p2m_open "NumberField P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "IsFiniteOrderHeckeChar idealMultiplicity AdmitsModulus"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

theorem isometry_finitePlaceEmbedding_withAbs (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (fun x : WithAbs (FinitePlace.mk v).1 =>
      FinitePlace.embedding v (WithAbs.equiv (FinitePlace.mk v).1 x)) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub (FinitePlace.embedding v),
    show WithAbs.equiv _ x - WithAbs.equiv _ y
      = WithAbs.ofAbs (v := (FinitePlace.mk v).1) (x - y) from (WithAbs.ofAbs_sub _ _ _).symm]
  exact (FinitePlace.mk_apply v (WithAbs.ofAbs (x - y))).symm

theorem valuation_le_of_adicAbv_le (v : HeightOneSpectrum (𝓞 K)) {x y : K}
    (h : NumberField.HeightOneSpectrum.adicAbv K v x
      ≤ NumberField.HeightOneSpectrum.adicAbv K v y) :
    v.valuation K x ≤ v.valuation K y := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, NumberField.HeightOneSpectrum.adicAbv_def] at h
  exact (WithZeroMulInt.toNNReal_strictMono
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le.mp
    (by exact_mod_cast h)

theorem sign_eq_of_withAbs_dist_lt (τ : K →+* ℝ) (α t : K) (ht : t ≠ 0)
    (h : (placeOf K τ).1 (α - t) < (placeOf K τ).1 t) :
    (0 < τ α ↔ 0 < τ t) := by

  have hval : ∀ x : K, (placeOf K τ).1 x = |τ x| := by
    intro x
    rw [← InfinitePlace.coe_apply]
    show (InfinitePlace.mk (Complex.ofRealHom.comp τ)) x = |τ x|
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hval, hval, map_sub] at h

  have ht0 : τ t ≠ 0 := fun h0 => ht ((map_eq_zero τ).mp h0)
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · refine ⟨fun hα => absurd ?_ (not_lt.mpr hα.le), fun hα => absurd hα hneg.not_gt⟩
    calc τ α = τ t + (τ α - τ t) := by ring
      _ < 0 := by
        have := abs_lt.mp h
        linarith [abs_of_neg hneg ▸ this.2]
  · refine ⟨fun _ => hpos, fun _ => ?_⟩
    calc (0 : ℝ) < τ t - |τ α - τ t| := by linarith [abs_of_pos hpos ▸ h]
      _ ≤ τ t - (τ t - τ α) := by linarith [neg_abs_le (τ α - τ t)]
      _ = τ α := by ring

noncomputable def primesOf (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot])).toFinset

theorem mem_primesOf {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ primesOf K 𝔣 h𝔣 ↔ v.asIdeal ∣ 𝔣 :=
  Set.Finite.mem_toFinset _

noncomputable def fadComp (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

theorem fadComp_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    fadComp K u v ≠ 0 := by
  intro h
  exact valued_ne_zero_of_unit K (projFin K u) v (by rw [projFin_val, ← fadComp, h, map_zero])

theorem archRealProjTau_principal (τ : K →+* ℝ) (α : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = τ (α : K) := by
  unfold archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_placeOf]
  rfl

theorem exists_embedding_near_fadComp (u : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < ε := by
  obtain ⟨t, ht⟩ := Metric.denseRange_iff.mp (v.denseRange_algebraMap K) (fadComp K u v) ε hε
  exact ⟨t, by rw [FinitePlace.embedding_apply]; rwa [dist_comm, dist_eq_norm] at ht⟩

theorem cong_of_completion_close {v : HeightOneSpectrum (𝓞 K)} {α : K} {U : v.adicCompletion K}
    (hU : U ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ‖FinitePlace.embedding v α - U‖ < ‖U‖ * δ) :
    ‖U * (FinitePlace.embedding v α)⁻¹‖ = 1 ∧
    ‖U * (FinitePlace.embedding v α)⁻¹ - 1‖ ≤ δ := by
  set αv := FinitePlace.embedding v α with hαv
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hlt : ‖αv - U‖ < ‖U‖ :=
    h.trans_le (by nlinarith)
  have hαeq : ‖αv‖ = ‖U‖ := by
    have hne : ‖U‖ ≠ ‖αv - U‖ := (hlt.trans_le (le_refl _)).ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := U) (y := αv - U) hne
    rw [add_sub_cancel, max_eq_left hlt.le] at this
    exact this
  have hα0 : αv ≠ 0 := fun h0 => by simp [h0] at hαeq; exact hU (norm_eq_zero.mp hαeq.symm)
  refine ⟨?_, ?_⟩
  · rw [norm_mul, norm_inv, hαeq, mul_inv_cancel₀ hUpos.ne']
  · have hfac : U * αv⁻¹ - 1 = (U - αv) * αv⁻¹ := by
      field_simp
    rw [hfac, norm_mul, norm_inv, hαeq, norm_sub_rev]
    calc ‖αv - U‖ * ‖U‖⁻¹ ≤ (‖U‖ * δ) * ‖U‖⁻¹ := by
          exact mul_le_mul_of_nonneg_right h.le (inv_nonneg.mpr hUpos.le)
      _ = δ := by field_simp

theorem adjCompEq (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
      = fadComp K u v * (FinitePlace.embedding v (α : K))⁻¹ := by
  have hmul : ((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      = (u : AdeleRing (𝓞 K) K).2
        * (((Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
    rw [Units.val_mul]; rfl
  rw [hmul, fad_mul_apply K, ← fadComp]
  congr 1
  rw [← map_inv, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val,
    FinitePlace.embedding_apply]
  show ((algebraMap K (AdeleRing (𝓞 K) K)) ((α : K)⁻¹)).2 v = _
  rw [show ∀ x : K, ((algebraMap K (AdeleRing (𝓞 K) K)) x).2 v
      = algebraMap K (v.adicCompletion K) x from fun x => rfl,
    map_inv₀]
  rfl

theorem valued_cong_of_norm_cong {v : HeightOneSpectrum (𝓞 K)} {X Y : v.adicCompletion K}
    (h1 : ‖X‖ = 1) (h2 : ‖X - 1‖ ≤ ‖Y‖) :
    Valued.v X = 1 ∧ Valued.v (X - 1) ≤ Valued.v Y := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact (Valued.toNormedField.norm_le_one_iff).mp h1.le
  · exact (Valued.toNormedField.one_le_norm_iff).mp h1.ge
  · exact (Valued.toNormedField.norm_le_iff).mp h2

theorem exists_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by
  classical
  set S := primesOf K 𝔣 h𝔣 with hS

  obtain ⟨γ, hγ𝔣, hγ0⟩ : ∃ γ : 𝓞 K, γ ∈ 𝔣 ∧ γ ≠ 0 := by
    obtain ⟨γ, hγ𝔣, hγ0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr h𝔣)
    exact ⟨γ, hγ𝔣, fun h => hγ0 (h ▸ Ideal.zero_mem ⊥)⟩
  have hγK0 : (γ : K) ≠ 0 := by exact_mod_cast hγ0

  have hγemb_ne : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.embedding v (γ : K) ≠ 0 :=
    fun v => (map_ne_zero _).mpr hγK0
  have hγnorm_pos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖FinitePlace.embedding v (γ : K)‖ :=
    fun v => norm_pos_iff.mpr (hγemb_ne v)
  have hγnorm_le_one : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖FinitePlace.embedding v (γ : K)‖ ≤ 1 := by
    intro v
    rw [Valued.toNormedField.norm_le_one_iff,
      show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one γ
  have hγval_le : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (FinitePlace.embedding v (γ : K))
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
    intro v _
    rw [show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    refine (v.intValuation_le_pow_iff_dvd γ _).mpr
      (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hγ𝔣))))
    have h𝔣0 : (Associates.mk 𝔣) ≠ 0 :=
      Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
    have hirr := Associates.irreducible_mk.mpr v.irreducible
    have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr
        (k := idealMultiplicity K v 𝔣)).mpr le_rfl
    rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this

  have hUpos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖fadComp K u v‖ :=
    fun v => norm_pos_iff.mpr (fadComp_ne_zero K u v)

  set bnd : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ with hbnd
  have hbnd_pos : ∀ v, 0 < bnd v := fun v => mul_pos (hUpos v) (hγnorm_pos v)
  obtain ⟨r, hr0, hr1, hrS⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ v ∈ S, r < bnd v := by
    by_cases hne : S.Nonempty
    · have hm_pos : 0 < S.inf' hne bnd :=
        (Finset.lt_inf'_iff hne).mpr (fun v _ => hbnd_pos v)
      refine ⟨min (1/2) (S.inf' hne bnd / 2), ?_, ?_, ?_⟩
      · exact lt_min (by norm_num) (by linarith)
      · exact (min_le_left _ _).trans_lt (by norm_num)
      · intro v hv
        refine (min_le_right _ _).trans_lt ?_
        have hle := Finset.inf'_le bnd hv
        linarith [hbnd_pos v]
    · exact ⟨1/2, by norm_num, by norm_num, fun v hv => absurd ⟨v, hv⟩ hne⟩

  have htv : ∀ v ∈ S, ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < r :=
    fun v _ => exists_embedding_near_fadComp K u v hr0
  choose tv htv using htv

  set archTgt : InfinitePlace K → K := fun w =>
    if hw : w.IsReal then
      (if archSign K (InfinitePlace.embedding_of_isReal hw) u then (1:K) else (-1:K))
    else (1:K) with harchTgt
  have harchTgt_ne : ∀ w, archTgt w ≠ 0 := by
    intro w; unfold archTgt; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero
  have harchTgt_abs : ∀ w : InfinitePlace K, w (archTgt w) = 1 := by
    intro w; unfold archTgt; split_ifs
    · exact map_one _
    · exact (w.1.map_neg 1).trans (map_one _)
    · exact map_one _

  set z : InfinitePlace K ⊕ ↥S → K := Sum.elim archTgt (fun v => tv v.1 v.2) with hz

  obtain ⟨α, hα⟩ := Metric.denseRange_iff.mp
    (NumberField.denseRange_algebraMap_pi_mixedAbs K S)
    (fun i => (WithAbs.equiv (NumberField.mixedAbs K S i)).symm (z i)) r hr0
  have hα_at : ∀ i, (NumberField.mixedAbs K S i) (α - z i) < r := by
    intro i
    have hi := (dist_pi_lt_iff hr0).mp hα i
    rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hi
    convert hi using 2
    rfl

  have hα0 : α ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    intro h
    have := hα_at (Sum.inl w)
    simp only [hz, Sum.elim_inl, h, zero_sub] at this
    have heq : (NumberField.mixedAbs K S (Sum.inl w)) (-archTgt w) = 1 := by
      change (w.1 : AbsoluteValue K ℝ) (-archTgt w) = 1
      rw [(w.1).map_neg, ← InfinitePlace.coe_apply, harchTgt_abs w]
    rw [heq] at this; linarith
  refine ⟨Units.mk0 α hα0, ?_, ?_⟩
  ·
    intro v hv
    have hvS : v ∈ S := (mem_primesOf K h𝔣 v).mpr hv
    rw [adjCompEq K u (Units.mk0 α hα0) v, Units.val_mk0]

    have hstep : ‖FinitePlace.embedding v α - fadComp K u v‖
        < ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ := by
      have hα_fin := hα_at (Sum.inr ⟨v, hvS⟩)
      simp only [hz, Sum.elim_inr, NumberField.mixedAbs] at hα_fin

      have h1 : ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖ < r := by
        rw [← map_sub]; exact hα_fin
      have h2 := htv v hvS
      calc ‖FinitePlace.embedding v α - fadComp K u v‖
          ≤ max ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖
              ‖FinitePlace.embedding v (tv v hvS) - fadComp K u v‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact IsUltrametricDist.dist_triangle_max _ _ _
        _ < r := max_lt h1 h2
        _ < bnd v := hrS v hvS
    have hcong := cong_of_completion_close K (fadComp_ne_zero K u v)
      (hγnorm_pos v) (hγnorm_le_one v) hstep
    have hbr := valued_cong_of_norm_cong K hcong.1 hcong.2
    exact ⟨hbr.1, hbr.2.trans (hγval_le v hv)⟩
  ·
    intro τ
    rw [archSign_mul K τ, archSign_inv K τ]
    show archSign K τ u ↔ archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.mk0 α hα0))
    unfold archSign
    rw [archRealProjTau_principal K τ (Units.mk0 α hα0), Units.val_mk0]

    have hwτ := isReal_placeOf K τ
    have htgt_τ : archTgt (placeOf K τ)
        = if (0:ℝ) < archRealProjTau K τ u then (1:K) else (-1:K) := by
      unfold archTgt; rw [dif_pos hwτ]
      congr 1
      · unfold archSign
        rw [show InfinitePlace.embedding_of_isReal hwτ = τ from embedding_of_isReal_placeOf K τ]
    have habs_tgt : (placeOf K τ) (archTgt (placeOf K τ)) = 1 := harchTgt_abs _
    have hclose : (placeOf K τ) (α - archTgt (placeOf K τ)) < (placeOf K τ) (archTgt (placeOf K τ)) := by
      rw [habs_tgt]
      have := hα_at (Sum.inl (placeOf K τ))
      simp only [hz, Sum.elim_inl, NumberField.mixedAbs] at this
      exact this.trans hr1
    have hsign_iff := sign_eq_of_withAbs_dist_lt K τ α (archTgt (placeOf K τ))
      (harchTgt_ne _) hclose
    constructor
    · intro hpos
      refine hsign_iff.mpr ?_
      rw [htgt_τ, if_pos hpos, map_one]; exact one_pos
    · intro hτα
      by_contra hneg
      have hlt : (0:ℝ) < -1 := by
        have := hsign_iff.mp hτα
        rwa [htgt_τ, if_neg hneg, map_neg, map_one] at this
      linarith

end HeckeCharacter

end Fold_ExistsAdjuster

section Fold_IdeleContent

p2m_open "NumberField P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "IsFiniteOrderHeckeChar idealMultiplicity AdmitsModulus"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

def ideleContentHom (𝔣 : Ideal (𝓞 K)) :
    (AdeleRing (𝓞 K) K)ˣ →* NarrowRayClassGroup K 𝔣 := by
  classical
  by_cases h𝔣 : 𝔣 = ⊥
  · exact 1
  · exact
      { toFun := fun u => NarrowRayClassGroup.mk K 𝔣
          ⟨_, (Classical.choose_spec (exists_isAdjuster K h𝔣 u)).coprime⟩
        map_one' := by
          rw [mk_eq_mk_of_isAdjuster K h𝔣
            (Classical.choose_spec (exists_isAdjuster K h𝔣 1)) (isAdjuster_one_one K 𝔣)]
          simp only [map_one, inv_one, mul_one]; rfl
        map_mul' := fun u u' => by
          have hαu := Classical.choose_spec (exists_isAdjuster K h𝔣 u)
          have hαu' := Classical.choose_spec (exists_isAdjuster K h𝔣 u')
          have hαuu' : IsAdjuster K 𝔣 (u * u') (_ * _) := IsAdjuster.mul K hαu hαu'
          rw [mk_eq_mk_of_isAdjuster K h𝔣
              (Classical.choose_spec (exists_isAdjuster K h𝔣 (u * u'))) hαuu',
            ← (NarrowRayClassGroup.mk K 𝔣).map_mul ⟨_, hαu.coprime⟩ ⟨_, hαu'.coprime⟩]
          refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
          show fadContentHom K (projFin K _) = fadContentHom K (projFin K _)
            * fadContentHom K (projFin K _)
          rw [← map_mul, ← map_mul, adj_adele_mul K u u'] }

theorem ideleContentHom_apply {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ} (hα : IsAdjuster K 𝔣 u α) :
    ideleContentHom K 𝔣 u = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩ := by
  unfold ideleContentHom
  rw [dif_neg h𝔣]
  exact mk_eq_mk_of_isAdjuster K h𝔣 (Classical.choose_spec (exists_isAdjuster K h𝔣 u)) hα

theorem ideleContentHom_principal (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    ideleContentHom K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = 1 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · unfold ideleContentHom; rw [dif_pos h𝔣]; rfl
  · rw [ideleContentHom_apply K h𝔣 (isAdjuster_principal_self K 𝔣 α)]
    have h1 : fadContentHom K (projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)) = 1 := by
      rw [mul_inv_cancel, map_one, map_one]
    rw [show (⟨_, (isAdjuster_principal_self K 𝔣 α).coprime⟩ : ↥(coprimeToModulus K 𝔣)) = 1
      from Subtype.ext h1, map_one]

theorem ideleContentHom_uniformizerIdele_v2 (𝔣 : Ideal (𝓞 K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1)
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w) = 1)
    (huv : Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = WithZero.exp (-1 : ℤ))
    (hu𝔣 : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w - 1)
        ≤ WithZero.exp (-(idealMultiplicity K w 𝔣 : ℤ))) :
    ideleContentHom K 𝔣 u = primeClass K 𝔣 v hv := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣; simp only [show v.asIdeal ∣ (⊥ : Ideal (𝓞 K)) from ⟨0, (mul_zero _).symm⟩,
      not_true] at hv
  ·
    have hadj : IsAdjuster K 𝔣 u 1 := by
      refine ⟨fun w hw𝔣 => ?_, fun τ => ?_⟩
      · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
        show Valued.v (adjFinV K u 1 w) = 1 ∧ Valued.v (adjFinV K u 1 w - 1) ≤ _
        have hu1 : adjFinV K u 1 w = (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)
            w) := by unfold adjFinV; simp only [map_one, inv_one, mul_one]
        rw [hu1]
        exact ⟨huw w hwv, hu𝔣 w hw𝔣⟩
      · simp only [map_one, inv_one, mul_one]
        exact archSign_of_fst_eq_one K τ huarch
    rw [ideleContentHom_apply K h𝔣 hadj]

    refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
    show fadContentHom K (projFin K (u * (pK K 1)⁻¹)) = primeUnit K v
    rw [map_one, inv_one, mul_one, fadContentHom_apply]
    refine finprod_eq_single (fun w => primeUnit K w ^ placeOrd K (projFin K u) w) v
      ?_ |>.trans ?_
    · intro w hwv
      show primeUnit K w ^ placeOrd K (projFin K u) w = 1
      rw [show placeOrd K (projFin K u) w = 0 from
        (placeOrd_eq_zero_iff K (projFin K u) w).mpr (projFin_val K u ▸ huw w hwv), zpow_zero]
    · show primeUnit K v ^ placeOrd K (projFin K u) v = primeUnit K v
      rw [show placeOrd K (projFin K u) v = 1 from by
        unfold placeOrd; rw [projFin_val, huv, WithZero.log_exp, neg_neg], zpow_one]

end HeckeCharacter

end

end Fold_IdeleContent

section Fold_PillarBricks

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.NumberField IsDedekindDomain Deep.NTSupply WithZero HeckeCharacter P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.HeckeCharacter"

noncomputable section

namespace M4aP2
namespace PillarBricks

section Unitary

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

theorem isUnitaryChar_of_isOfFinOrder {η : (AdeleRing R F)ˣ →* ℂˣ} (hη : IsOfFinOrder η) :
    AutomorphicForm.IsUnitaryChar R F η := by
  intro x
  obtain ⟨n, hn, hη1⟩ := isOfFinOrder_iff_pow_eq_one.mp hη
  have hxn : ((η x : ℂˣ) : ℂ) ^ n = 1 := by
    calc ((η x : ℂˣ) : ℂ) ^ n = (((η x ^ n : ℂˣ)) : ℂ) := (Units.val_pow_eq_pow_val _ _).symm
      _ = (((η ^ n) x : ℂˣ) : ℂ) := by rw [MonoidHom.pow_apply]
      _ = ((1 : ℂˣ) : ℂ) := by rw [hη1, MonoidHom.one_apply]
      _ = 1 := Units.val_one
  have hnorm : ‖((η x : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, hxn, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp hnorm

end Unitary

section General

variable (K : Type*) [Field K] [NumberField K]

theorem ideleContentHom_apply_of_eq_bot {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 = ⊥)
    (u : (AdeleRing (𝓞 K) K)ˣ) : ideleContentHom K 𝔣 u = 1 := by
  unfold ideleContentHom; rw [dif_pos h𝔣]; rfl

theorem isOfFinOrder_comp_ideleContentHom {M : Type*} [CommGroup M] (𝔣 : Ideal (𝓞 K))
    (χ : NarrowRayClassGroup K 𝔣 →* M) : IsOfFinOrder (χ.comp (ideleContentHom K 𝔣)) := by
  by_cases h𝔣 : 𝔣 = ⊥
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, MonoidHom.ext fun u => ?_⟩
    rw [pow_one, MonoidHom.comp_apply, ideleContentHom_apply_of_eq_bot K h𝔣 u, map_one,
      MonoidHom.one_apply]
  · haveI := Deep.NTSupply.finite (K := K) h𝔣
    refine isOfFinOrder_iff_pow_eq_one.mpr
      ⟨Nat.card (NarrowRayClassGroup K 𝔣), Nat.card_pos, MonoidHom.ext fun u => ?_⟩
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one,
      MonoidHom.one_apply]

theorem isUnitaryChar_comp_ideleContentHom (𝔣 : Ideal (𝓞 K))
    (χ : NarrowRayClassGroup K 𝔣 →* ℂˣ) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (χ.comp (ideleContentHom K 𝔣)) :=
  isUnitaryChar_of_isOfFinOrder (isOfFinOrder_comp_ideleContentHom K 𝔣 χ)

theorem ideleContentHom_eq_one_of_archSign (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hsign : ∀ τ : K →+* ℝ, archSign K τ u)
    (hunit : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v - 1)
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    ideleContentHom K 𝔣 u = 1 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · exact ideleContentHom_apply_of_eq_bot K h𝔣 u
  · have h1 : u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (1 : Kˣ))⁻¹ = u := by
      rw [map_one, inv_one, mul_one]
    have hadj : IsAdjuster K 𝔣 u 1 := by
      refine ⟨fun v hv𝔣 => ?_, fun τ => ?_⟩
      · rw [h1]
        exact ⟨hunit v, hcong v hv𝔣⟩
      · rw [h1]
        exact hsign τ
    have hcontent : fadContentHom K (projFin K
        (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (1 : Kˣ))⁻¹)) = 1 := by
      rw [h1, fadContentHom_apply]
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      rw [(placeOrd_eq_zero_iff K (projFin K u) w).mpr (projFin_val K u ▸ hunit w), zpow_zero]
    rw [ideleContentHom_apply K h𝔣 hadj,
      show (⟨_, hadj.coprime⟩ : ↥(coprimeToModulus K 𝔣)) = 1 from Subtype.ext hcontent, map_one]

theorem ideleContentHom_eq_one_of_cong (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 ∧
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v - 1)
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    ideleContentHom K 𝔣 u = 1 :=
  ideleContentHom_eq_one_of_archSign K 𝔣 u (fun τ => archSign_of_fst_eq_one K τ huarch)
    (fun v => (hu v).1) (fun v _ => (hu v).2)

theorem admitsModulus_comp_ideleContentHom (𝔣 : Ideal (𝓞 K))
    (χ : NarrowRayClassGroup K 𝔣 →* ℂˣ) :
    AdmitsModulus K (χ.comp (ideleContentHom K 𝔣)) 𝔣 := by
  intro u huarch hu
  rw [MonoidHom.comp_apply, ideleContentHom_eq_one_of_cong K 𝔣 u huarch hu, map_one]

theorem idealBound_eq_exp_neg_idealMultiplicity {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.AdelicLevel.idealBound (𝓞 K) 𝔣 v
      = WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
  classical
  rw [NumberField.AdelicLevel.idealBound_of_ne_bot h𝔣]
  rfl

theorem isOpen_setOf_realPos :
    IsOpen {u : (AdeleRing (𝓞 K) K)ˣ | ∀ w : {w : InfinitePlace K // w.IsReal},
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((u : AdeleRing (𝓞 K) K).1 w.1)} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun w => ?_
  have hc : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((u : AdeleRing (𝓞 K) K).1 w.1) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
      ((NumberField.AdelicLevel.continuous_archEval K w.1).comp
        ((NumberField.AdelicLevel.continuous_adeleArch (𝓞 K) K).comp Units.continuous_val))
  exact isOpen_lt continuous_const hc

theorem valuation_eq_one_of_integral_of_inv_integral (u : (AdeleRing (𝓞 K) K)ˣ)
    (hint : (u : AdeleRing (𝓞 K) K).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hinv : ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 := by
  have hx := NumberField.AdelicLevel.valued_apply_le_one hint v
  have hy := NumberField.AdelicLevel.valued_apply_le_one hinv v
  have hmul : (u : AdeleRing (𝓞 K) K).2 v
      * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    congrArg (fun x : AdeleRing (𝓞 K) K => x.2 v) u.mul_inv
  have hvmul : Valued.v ((u : AdeleRing (𝓞 K) K).2 v)
      * Valued.v (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm hx ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v ((u : AdeleRing (𝓞 K) K).2 v)
          * Valued.v (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) := hvmul.symm
    _ ≤ Valued.v ((u : AdeleRing (𝓞 K) K).2 v) * 1 := mul_le_mul_right hy _
    _ = Valued.v ((u : AdeleRing (𝓞 K) K).2 v) := mul_one _

theorem exists_isOpen_ideleContentHom_eq_one (𝔣 : Ideal (𝓞 K)) :
    ∃ U : Set (AdeleRing (𝓞 K) K)ˣ, IsOpen U ∧ (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ U ∧
      ∀ u ∈ U, ideleContentHom K 𝔣 u = 1 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun u _ => ideleContentHom_apply_of_eq_bot K h𝔣 u⟩
  · refine ⟨{u | ∀ w : {w : InfinitePlace K // w.IsReal},
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((u : AdeleRing (𝓞 K) K).1 w.1)} ∩
      ({u | (u : AdeleRing (𝓞 K) K).2 - 1 ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K 𝔣} ∩
        {u | ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K}), ?_, ?_, ?_⟩
    ·
      refine (isOpen_setOf_realPos K).inter (IsOpen.inter ?_ ?_)
      · have hc : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ => (u : AdeleRing (𝓞 K) K).2 - 1 :=
          ((NumberField.AdelicLevel.continuous_adeleFin (𝓞 K) K).comp Units.continuous_val).sub
            continuous_const
        exact (NumberField.AdelicLevel.isOpen_idealBall (𝓞 K) K h𝔣).preimage hc
      · have hc : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
            ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :=
          (NumberField.AdelicLevel.continuous_adeleFin (𝓞 K) K).comp Units.continuous_coe_inv
        exact (NumberField.AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K).preimage hc
    ·
      have h1arch : ∀ w : InfinitePlace K,
          ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := fun _ => rfl
      have h1fin : ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl
      have h1inv : (((1 : (AdeleRing (𝓞 K) K)ˣ)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
          = 1 := rfl
      refine ⟨fun w => ?_, ?_, ?_⟩
      · rw [h1arch w.1, map_one]
        exact one_pos
      · show ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 - 1
          ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K 𝔣
        rw [h1fin, sub_self]
        exact NumberField.AdelicLevel.zero_mem_idealBall 𝔣
      · show (((1 : (AdeleRing (𝓞 K) K)ˣ)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K
        rw [h1inv]
        exact NumberField.AdelicLevel.one_mem_integralFiniteAdeles
    ·
      rintro u ⟨hpos, hball, hinv⟩
      have hint : (u : AdeleRing (𝓞 K) K).2
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
        have h := NumberField.AdelicLevel.add_mem_integralFiniteAdeles
          (NumberField.AdelicLevel.idealBall_subset_integralFiniteAdeles 𝔣 hball)
          (NumberField.AdelicLevel.one_mem_integralFiniteAdeles (R := 𝓞 K) (K := K))
        rwa [sub_add_cancel] at h
      have hunit : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 :=
        fun v => valuation_eq_one_of_integral_of_inv_integral K u hint hinv v
      refine ideleContentHom_eq_one_of_archSign K 𝔣 u (fun τ => ?_) hunit (fun v hv𝔣 => ?_)
      · show 0 < archRealProjTau K τ u
        unfold archRealProjTau
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact hpos ⟨placeOf K τ, isReal_placeOf K τ⟩
      · have h := hball v
        rw [idealBound_eq_exp_neg_idealMultiplicity K h𝔣 v] at h
        exact h

theorem continuous_comp_ideleContentHom (𝔣 : Ideal (𝓞 K))
    (χ : NarrowRayClassGroup K 𝔣 →* ℂˣ) :
    Continuous (χ.comp (ideleContentHom K 𝔣)) := by
  obtain ⟨U, hU, h1, hU1⟩ := exists_isOpen_ideleContentHom_eq_one K 𝔣
  have hev : (fun _ => (1 : ℂˣ)) =ᶠ[nhds (1 : (AdeleRing (𝓞 K) K)ˣ)]
      (χ.comp (ideleContentHom K 𝔣)) :=
    Filter.eventually_of_mem (hU.mem_nhds h1) fun u hu => by
      rw [MonoidHom.comp_apply, hU1 u hu, map_one]
  refine continuous_of_continuousAt_one (χ.comp (ideleContentHom K 𝔣)) ?_
  show Filter.Tendsto _ (nhds 1) (nhds ((χ.comp (ideleContentHom K 𝔣)) 1))
  rw [map_one]
  exact tendsto_const_nhds.congr' hev

end General

section Value

variable (K : Type) [Field K] [NumberField K]

theorem ideleContentHom_uniformizerIdele (𝔣 : Ideal (𝓞 K)) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔣) :
    ideleContentHom K 𝔣 (AutomorphicForm.uniformizerIdele K v) = primeClass K 𝔣 v hv := by

  have hfin : ∀ w : HeightOneSpectrum (𝓞 K),
      ((AutomorphicForm.uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w
        = ((NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)
            : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w := fun _ => rfl
  have hof_ne : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      ((AutomorphicForm.uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 :=
    fun w hw => (hfin w).trans (NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 K) K v _ hw)
  refine ideleContentHom_uniformizerIdele_v2 K 𝔣 hv _ rfl ?_ ?_ ?_
  · intro w hw
    rw [hof_ne w hw, map_one]
  · rw [hfin v, NumberField.AdelicLevel.localUnit_apply_self]
    exact NumberField.AdelicLevel.valued_uniformizerUnit K v
  · intro w hw𝔣
    rw [hof_ne w (fun h => hv (h ▸ hw𝔣)), sub_self, map_zero]
    exact zero_le'

theorem exists_heckeCharOfRayClassChar_of_bricks
    (𝔣 : Ideal (NumberField.RingOfIntegers K))
    (χ : Deep.NTSupply.NarrowRayClassGroup K 𝔣 →* ℂˣ) :
    ∃ η : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar K η ∧
      HeckeCharacter.AdmitsModulus K η 𝔣 ∧
      AutomorphicForm.IsUnitaryChar (NumberField.RingOfIntegers K) K η ∧
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        (hv : ¬ v.asIdeal ∣ 𝔣),
        η (AutomorphicForm.uniformizerIdele K v)
          = χ (Deep.NTSupply.primeClass K 𝔣 v hv) := by
  refine ⟨χ.comp (ideleContentHom K 𝔣), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro q
    rw [MonoidHom.comp_apply, ideleContentHom_principal, map_one]
  · exact continuous_comp_ideleContentHom K 𝔣 χ
  · exact isOfFinOrder_comp_ideleContentHom K 𝔣 χ
  · exact admitsModulus_comp_ideleContentHom K 𝔣 χ
  · exact isUnitaryChar_comp_ideleContentHom K 𝔣 χ
  · intro v hv
    rw [MonoidHom.comp_apply, ideleContentHom_uniformizerIdele K 𝔣 hv]

end Value

end M4aP2.PillarBricks

end

end Fold_PillarBricks

theorem solution
    (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (NumberField.RingOfIntegers K))
    (χ : Deep.NTSupply.NarrowRayClassGroup K 𝔣 →* ℂˣ) :
    ∃ η : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar K η ∧
      HeckeCharacter.AdmitsModulus K η 𝔣 ∧
      AutomorphicForm.IsUnitaryChar (NumberField.RingOfIntegers K) K η ∧
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        (hv : ¬ v.asIdeal ∣ 𝔣),
        η (AutomorphicForm.uniformizerIdele K v)
          = χ (Deep.NTSupply.primeClass K 𝔣 v hv) :=
  M4aP2.PillarBricks.exists_heckeCharOfRayClassChar_of_bricks K 𝔣 χ

#print axioms solution

end S_LT_HeckeChar_exists_heckeCharOfRayClassChar
end P2MW
export P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar (solution)
