-- Prove2me | solution 1 for IsLocalRing.exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a568dc93-bee9-542a-b584-5fe6981d1f5c

import Mathlib
import Theorems.Thm_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "IsLocalRing P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber.IsLocalRing TrivSqZeroExt"

universe u v

namespace IsLocalRing
p2m_export "IsLocalRing" "CotangentSpace eq_maximalIdeal ResidueField map_maximalIdeal_le maximalIdeal residue_eq_zero_iff residue_surjective ResidueField.algebraMap_eq residue exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map"
namespace HullFromTangentAux
p2m_open "IsLocalRing"

section Basic

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
variable {R : Type v} [CommRing R] [IsLocalRing R] [Algebra Λ R]

lemma ker_residue_comp_eq (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) :
    RingHom.ker ((residue R).comp (algebraMap Λ R)) = maximalIdeal Λ :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hres)

lemma residue_algebraMap_eq_zero_iff (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (μ : Λ) : residue R (algebraMap Λ R μ) = 0 ↔ μ ∈ maximalIdeal Λ := by
  rw [← ker_residue_comp_eq hres, RingHom.mem_ker, RingHom.comp_apply]

lemma algebraMap_mem_maximalIdeal (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    {μ : Λ} (hμ : μ ∈ maximalIdeal Λ) : algebraMap Λ R μ ∈ maximalIdeal R := by
  rw [← residue_eq_zero_iff]
  exact (residue_algebraMap_eq_zero_iff hres μ).2 hμ

lemma map_maximalIdeal_le (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) :
    (maximalIdeal Λ).map (algebraMap Λ R) ≤ maximalIdeal R :=
  Ideal.map_le_iff_le_comap.2 fun _ hμ => algebraMap_mem_maximalIdeal hres hμ

lemma residue_eq_zero_of_mem_map (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    {y : R} (hy : y ∈ (maximalIdeal Λ).map (algebraMap Λ R)) : residue R y = 0 :=
  (residue_eq_zero_iff y).2 (map_maximalIdeal_le hres hy)

lemma algebraMap_dualNumber_apply (μ : Λ) :
    algebraMap Λ (DualNumber (ResidueField R)) μ = inl (residue R (algebraMap Λ R μ)) := by
  rw [TrivSqZeroExt.algebraMap_eq_inl', IsScalarTower.algebraMap_apply Λ R (ResidueField R)]
  rfl

noncomputable def sec (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r : R) : Λ :=
  Classical.choose (hres (residue R r))

lemma residue_algebraMap_sec (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r : R) :
    residue R (algebraMap Λ R (sec hres r)) = residue R r :=
  Classical.choose_spec (hres (residue R r))

lemma sub_algebraMap_mem (_hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r : R)
    (μ : Λ) (hμ : residue R (algebraMap Λ R μ) = residue R r) :
    r - algebraMap Λ R μ ∈ maximalIdeal R := by
  rw [← residue_eq_zero_iff, map_sub, hμ, sub_self]

lemma sub_sec_mem (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r : R) :
    r - algebraMap Λ R (sec hres r) ∈ maximalIdeal R :=
  sub_algebraMap_mem hres r _ (residue_algebraMap_sec hres r)

lemma algebraMap_sub_mem_map (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (μ ν : Λ) (h : residue R (algebraMap Λ R μ) = residue R (algebraMap Λ R ν)) :
    algebraMap Λ R μ - algebraMap Λ R ν ∈ (maximalIdeal Λ).map (algebraMap Λ R) := by
  rw [← map_sub]
  refine Ideal.mem_map_of_mem _ ((residue_algebraMap_eq_zero_iff hres _).1 ?_)
  rw [map_sub, map_sub, h, sub_self]

def NΛ (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] (R : Type v) [CommRing R] [IsLocalRing R] [Algebra Λ R] :
    Submodule R (maximalIdeal R) :=
  Submodule.comap (maximalIdeal R).subtype ((maximalIdeal Λ).map (algebraMap Λ R))

lemma mem_NΛ {x : maximalIdeal R} :
    x ∈ NΛ Λ R ↔ (x : R) ∈ (maximalIdeal Λ).map (algebraMap Λ R) := Iff.rfl

noncomputable def W (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] (R : Type v) [CommRing R] [IsLocalRing R]
    [Algebra Λ R] : Submodule (ResidueField R) (CotangentSpace R) :=
  Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' (NΛ Λ R : Set (maximalIdeal R)))

lemma toCotangent_mem_W {x : maximalIdeal R} (hx : x ∈ NΛ Λ R) :
    (maximalIdeal R).toCotangent x ∈ W Λ R :=
  Submodule.subset_span ⟨x, hx, rfl⟩

lemma smul_toCotangent (r : R) (x : maximalIdeal R) :
    residue R r • (maximalIdeal R).toCotangent x = (maximalIdeal R).toCotangent (r • x) := by
  rw [map_smul, ← IsScalarTower.algebraMap_smul (ResidueField R) r]
  rfl

lemma exists_of_mem_W {z : CotangentSpace R} (hz : z ∈ W Λ R) :
    ∃ n : maximalIdeal R, n ∈ NΛ Λ R ∧ (maximalIdeal R).toCotangent n = z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, hn, rfl⟩ := hx
    exact ⟨n, hn, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, rfl⟩ := hx
    obtain ⟨n₂, hn₂, rfl⟩ := hy
    exact ⟨n₁ + n₂, Submodule.add_mem _ hn₁ hn₂, map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨n, hn, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨r • n, Submodule.smul_mem _ r hn, (smul_toCotangent r n).symm⟩

abbrev V (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] (R : Type v) [CommRing R] [IsLocalRing R]
    [Algebra Λ R] : Type v :=
  CotangentSpace R ⧸ W Λ R

noncomputable def cls (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] (R : Type v) [CommRing R] [IsLocalRing R]
    [Algebra Λ R] (x : maximalIdeal R) : V Λ R :=
  (W Λ R).mkQ ((maximalIdeal R).toCotangent x)

lemma cls_add (x y : maximalIdeal R) : cls Λ R (x + y) = cls Λ R x + cls Λ R y := by
  simp only [cls, map_add]

lemma cls_smul (r : R) (x : maximalIdeal R) : cls Λ R (r • x) = residue R r • cls Λ R x := by
  simp only [cls]
  rw [← smul_toCotangent, map_smul]

lemma cls_sub (x y : maximalIdeal R) : cls Λ R x - cls Λ R y = cls Λ R (x - y) := by
  simp only [cls, map_sub]

lemma cls_eq_zero_of_mem_NΛ {x : maximalIdeal R} (hx : x ∈ NΛ Λ R) : cls Λ R x = 0 := by
  simp only [cls, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact toCotangent_mem_W hx

lemma cls_eq_zero_of_mem_sq {x : maximalIdeal R} (hx : (x : R) ∈ maximalIdeal R ^ 2) : cls Λ R x = 0 := by
  simp only [cls, Submodule.mkQ_apply]
  rw [(Ideal.toCotangent_eq_zero _ x).2 hx, Submodule.Quotient.mk_zero]

lemma cls_surjective : Function.Surjective (cls Λ R) :=
  (Submodule.mkQ_surjective _).comp (Ideal.toCotangent_surjective _)

lemma mem_sup_of_cls_eq_zero {x : maximalIdeal R} (hx : cls Λ R x = 0) :
    (x : R) ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R) := by
  simp only [cls, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨n, hn, hnx⟩ := exists_of_mem_W hx
  have hsq : ((x - n : maximalIdeal R) : R) ∈ maximalIdeal R ^ 2 :=
    ((maximalIdeal R).toCotangent_eq).1 hnx.symm
  have : (x : R) = (x - n : maximalIdeal R) + (n : R) := by
    simp only [AddSubgroupClass.coe_sub, sub_add_cancel]
  rw [this]
  exact Submodule.add_mem_sup hsq (mem_NΛ.1 hn)

noncomputable def D (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r : R) : V Λ R :=
  cls Λ R ⟨r - algebraMap Λ R (sec hres r), sub_sec_mem hres r⟩

lemma D_eq (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r : R) (μ : Λ)
    (hμ : residue R (algebraMap Λ R μ) = residue R r) :
    D hres r = cls Λ R ⟨r - algebraMap Λ R μ, sub_algebraMap_mem hres r μ hμ⟩ := by
  unfold D
  rw [← sub_eq_zero, cls_sub]
  refine cls_eq_zero_of_mem_NΛ (mem_NΛ.2 ?_)
  have : ((⟨r - algebraMap Λ R (sec hres r), sub_sec_mem hres r⟩ -
      ⟨r - algebraMap Λ R μ, sub_algebraMap_mem hres r μ hμ⟩ : maximalIdeal R) : R) =
      algebraMap Λ R μ - algebraMap Λ R (sec hres r) := by
    simp only [AddSubgroupClass.coe_sub]
    ring
  rw [this]
  exact algebraMap_sub_mem_map hres _ _ (by rw [hμ, residue_algebraMap_sec])

lemma D_algebraMap (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (μ : Λ) :
    D hres (algebraMap Λ R μ) = 0 := by
  rw [D_eq hres (algebraMap Λ R μ) μ rfl]
  have : (⟨algebraMap Λ R μ - algebraMap Λ R μ, sub_algebraMap_mem hres _ μ rfl⟩ : maximalIdeal R) = 0 :=
    Subtype.ext (sub_self _)
  rw [this, cls, map_zero, map_zero]

lemma D_one (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) : D hres 1 = 0 := by
  rw [← map_one (algebraMap Λ R)]
  exact D_algebraMap hres 1

lemma D_add (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r s : R) :
    D hres (r + s) = D hres r + D hres s := by
  have h : residue R (algebraMap Λ R (sec hres r + sec hres s)) = residue R (r + s) := by
    rw [map_add, map_add, map_add, residue_algebraMap_sec, residue_algebraMap_sec]
  rw [D_eq hres (r + s) _ h]
  unfold D
  rw [← cls_add]
  congr 1
  refine Subtype.ext ?_
  simp only [map_add, AddMemClass.coe_add]
  ring

lemma D_zero (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) : D hres 0 = 0 := by
  rw [← map_zero (algebraMap Λ R)]
  exact D_algebraMap hres 0

lemma D_mul (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) (r s : R) :
    D hres (r * s) = residue R r • D hres s + residue R s • D hres r := by
  have h : residue R (algebraMap Λ R (sec hres r * sec hres s)) = residue R (r * s) := by
    rw [map_mul, map_mul, map_mul, residue_algebraMap_sec, residue_algebraMap_sec]
  rw [D_eq hres (r * s) _ h]
  unfold D
  rw [← residue_algebraMap_sec hres s, ← cls_smul, ← cls_smul, ← cls_add]
  congr 1
  refine Subtype.ext ?_
  simp only [map_mul, AddMemClass.coe_add, SetLike.val_smul, smul_eq_mul]
  ring

lemma D_of_mem (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) {r : R}
    (hr : r ∈ maximalIdeal R) : D hres r = cls Λ R ⟨r, hr⟩ := by
  have h : residue R (algebraMap Λ R 0) = residue R r := by
    rw [map_zero, map_zero, eq_comm, residue_eq_zero_iff]; exact hr
  rw [D_eq hres r 0 h]
  congr 1
  exact Subtype.ext (by simp)

lemma D_surjective (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R))) :
    Function.Surjective (D hres) := by
  intro v
  obtain ⟨x, rfl⟩ := cls_surjective (Λ := Λ) (R := R) v
  exact ⟨x, D_of_mem hres x.2⟩

noncomputable def Φof (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (lam : V Λ R →ₗ[ResidueField R] ResidueField R) : R →ₐ[Λ] DualNumber (ResidueField R) where
  toFun r := inl (residue R r) + inr (lam (D hres r))
  map_one' := by
    rw [map_one, D_one, map_zero, inr_zero, add_zero, inl_one]
  map_mul' r s := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [map_mul]
    · simp only [snd_add, snd_inl, snd_inr, zero_add, snd_mul, fst_add, fst_inl, fst_inr, add_zero,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, D_mul, map_add, map_smul]
      ring
  map_zero' := by
    rw [map_zero, D_zero, map_zero, inl_zero, inr_zero, add_zero]
  map_add' r s := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [map_add]
    · simp [D_add]
  commutes' μ := by
    rw [algebraMap_dualNumber_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [D_algebraMap]

lemma Φof_fst (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (lam : V Λ R →ₗ[ResidueField R] ResidueField R) (r : R) : (Φof hres lam r).fst = residue R r := by
  simp [Φof]

lemma Φof_snd (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (lam : V Λ R →ₗ[ResidueField R] ResidueField R) (r : R) : (Φof hres lam r).snd = lam (D hres r) := by
  simp [Φof]

section FromHom

variable (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
  (Φ : R →ₐ[Λ] DualNumber (ResidueField R)) (hΦ : ∀ r, (Φ r).fst = residue R r)

include hΦ in
private lemma _root_.IsLocalRing.HullFromTangentAux.snd_mul (r s : R) : (Φ (r * s)).snd = residue R r * (Φ s).snd + residue R s * (Φ r).snd := by
  rw [map_mul, TrivSqZeroExt.snd_mul, hΦ, hΦ, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

p2m_export "IsLocalRing.HullFromTangentAux" "snd_mul"
lemma snd_algebraMap (μ : Λ) : (Φ (algebraMap Λ R μ)).snd = 0 := by
  rw [AlgHom.commutes, algebraMap_dualNumber_apply, snd_inl]

include hΦ in
lemma snd_eq_zero_of_mem_sq {y : R} (hy : y ∈ maximalIdeal R ^ 2) : (Φ y).snd = 0 := by
  rw [pow_two] at hy
  refine Submodule.mul_induction_on hy (fun m hm n hn => ?_) (fun x y hx hy => ?_)
  · rw [snd_mul Φ hΦ, (residue_eq_zero_iff m).2 hm, (residue_eq_zero_iff n).2 hn, zero_mul, zero_mul,
      add_zero]
  · rw [map_add, snd_add, hx, hy, add_zero]

include hres hΦ in
lemma snd_eq_zero_of_mem_map {y : R} (hy : y ∈ (maximalIdeal Λ).map (algebraMap Λ R)) : (Φ y).snd = 0 := by
  have key : ∀ z, z ∈ (maximalIdeal Λ).map (algebraMap Λ R) → (Φ z).snd = 0 := by
    intro z hz
    unfold Ideal.map at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨μ, -, rfl⟩ := hx
      exact snd_algebraMap Φ μ
    | zero => rw [map_zero, snd_zero]
    | add x y _ _ hx hy => rw [map_add, snd_add, hx, hy, add_zero]
    | smul r x hx' hx =>
      have hxm : residue R x = 0 := residue_eq_zero_of_mem_map hres hx'
      rw [smul_eq_mul, snd_mul Φ hΦ, hx, hxm, mul_zero, zero_mul, add_zero]
  exact key y hy

include hres hΦ in
lemma snd_eq_zero_of_mem_sup {y : R} (hy : y ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R)) :
    (Φ y).snd = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, snd_add, snd_eq_zero_of_mem_sq Φ hΦ ha, snd_eq_zero_of_mem_map hres Φ hΦ hb, add_zero]

noncomputable def sndLin : maximalIdeal R →ₗ[R] ResidueField R where
  toFun x := (Φ (x : R)).snd
  map_add' x y := by
    simp only [AddMemClass.coe_add, map_add, snd_add]
  map_smul' r x := by
    simp only [SetLike.val_smul, smul_eq_mul, RingHom.id_apply]
    rw [snd_mul Φ hΦ, (residue_eq_zero_iff (x : R)).2 x.2, zero_mul, add_zero, Algebra.smul_def]
    rfl

lemma sndLin_apply (x : maximalIdeal R) : sndLin Φ hΦ x = (Φ (x : R)).snd := rfl

noncomputable def sndCot : CotangentSpace R →ₗ[R] ResidueField R :=
  Ideal.Cotangent.lift (sndLin Φ hΦ) (fun x y => by
    rw [sndLin_apply]
    exact snd_eq_zero_of_mem_sq Φ hΦ (by rw [pow_two]; exact Ideal.mul_mem_mul x.2 y.2))

lemma sndCot_toCotangent (x : maximalIdeal R) :
    sndCot Φ hΦ ((maximalIdeal R).toCotangent x) = (Φ (x : R)).snd := rfl

noncomputable def sndCotK : CotangentSpace R →ₗ[ResidueField R] ResidueField R where
  toFun := sndCot Φ hΦ
  map_add' x y := map_add _ _ _
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := residue_surjective c
    rw [RingHom.id_apply, ← ResidueField.algebraMap_eq, algebraMap_smul, map_smul, algebraMap_smul]

lemma sndCotK_apply (x : CotangentSpace R) : sndCotK Φ hΦ x = sndCot Φ hΦ x := rfl

include hres in
lemma W_le_ker : W Λ R ≤ LinearMap.ker (sndCotK Φ hΦ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, hn, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, sndCotK_apply, sndCot_toCotangent]
  exact snd_eq_zero_of_mem_map hres Φ hΦ (mem_NΛ.1 hn)

noncomputable def lamOf : V Λ R →ₗ[ResidueField R] ResidueField R :=
  (W Λ R).liftQ (sndCotK Φ hΦ) (W_le_ker hres Φ hΦ)

lemma lamOf_cls (x : maximalIdeal R) : lamOf hres Φ hΦ (cls Λ R x) = (Φ (x : R)).snd := rfl

lemma lamOf_D (r : R) : lamOf hres Φ hΦ (D hres r) = (Φ r).snd := by
  unfold D
  rw [lamOf_cls, map_sub, snd_sub, snd_algebraMap, sub_zero]

end FromHom

end Basic

section Count

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
variable {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Λ R]
  (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
  (Φ₁ : R →ₐ[Λ] DualNumber (ResidueField R)) (hΦ₁ : ∀ r, (Φ₁ r).fst = residue R r)
  (hdim : ∀ Φ : R →ₐ[Λ] DualNumber (ResidueField R), (∀ r, (Φ r).fst = residue R r) →
    ∃ c : ResidueField R, ∀ r, (Φ r).snd = c * (Φ₁ r).snd)

include hdim in

lemma exists_eq_smul_lamOf (lam : V Λ R →ₗ[ResidueField R] ResidueField R) :
    ∃ c : ResidueField R, c • lamOf hres Φ₁ hΦ₁ = lam := by
  obtain ⟨c, hc⟩ := hdim (Φof hres lam) (Φof_fst hres lam)
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  obtain ⟨r, rfl⟩ := D_surjective hres v
  rw [LinearMap.smul_apply, lamOf_D, smul_eq_mul, ← hc, Φof_snd]

include hdim hΦ₁ Φ₁ hres in
lemma finrank_V_le_one : Module.finrank (ResidueField R) (V Λ R) ≤ 1 := by
  rw [← Subspace.dual_finrank_eq]
  exact finrank_le_one (lamOf hres Φ₁ hΦ₁) (exists_eq_smul_lamOf hres Φ₁ hΦ₁ hdim)

include hdim hΦ₁ in

lemma exists_smul_D_eq {t : R} (ht : D hres t ≠ 0) (v : V Λ R) :
    ∃ c : ResidueField R, c • D hres t = v := by
  have h1 : Module.finrank (ResidueField R) (V Λ R) = 1 := by
    refine le_antisymm (finrank_V_le_one hres Φ₁ hΦ₁ hdim) ?_
    exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨D hres t, ht⟩
  exact (finrank_eq_one_iff_of_nonzero' (D hres t) ht).1 h1 v

end Count

end IsLocalRing.HullFromTangentAux

open IsLocalRing.HullFromTangentAux in

theorem solution
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra Λ R] (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (hsmooth : ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
        [IsArtinianRing A] [IsArtinianRing B] [Algebra Λ A] [Algebra Λ B],
        Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap Λ A)) →
        Function.Surjective (⇑(residue B) ∘ ⇑(algebraMap Λ B)) →
        ∀ π : B →ₐ[Λ] A, Function.Surjective π →
        (∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal B, x * y = 0) →
        ∀ g : R →ₐ[Λ] A, ∃ g' : R →ₐ[Λ] B, π.comp g' = g)
    (Φ₁ : R →ₐ[Λ] DualNumber (ResidueField R)) (hΦ₁ : ∀ r, (Φ₁ r).fst = residue R r)
    (hΦ₁' : ∃ r, (Φ₁ r).snd ≠ 0)
    (hdim : ∀ Φ : R →ₐ[Λ] DualNumber (ResidueField R), (∀ r, (Φ r).fst = residue R r) →
      ∃ c : ResidueField R, ∀ r, (Φ r).snd = c * (Φ₁ r).snd) :
    ∃ e : PowerSeries Λ ≃ₐ[Λ] R, (Φ₁ (e PowerSeries.X)).snd ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ := hΦ₁'

  set t : R := r₀ - algebraMap Λ R (sec hres r₀) with ht_def
  have htm : t ∈ maximalIdeal R := sub_sec_mem hres r₀
  have hΦt : (Φ₁ t).snd = (Φ₁ r₀).snd := by
    rw [ht_def, map_sub, snd_sub, snd_algebraMap, sub_zero]
  have hDt : D hres t ≠ 0 := by
    intro h0
    apply hr₀
    rw [← hΦt, ← lamOf_D hres Φ₁ hΦ₁ t, h0, map_zero]

  have hgen : maximalIdeal R ≤ Ideal.span {t} ⊔ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R) := by
    intro m hm
    obtain ⟨c, hc⟩ := exists_smul_D_eq hres Φ₁ hΦ₁ hdim hDt (D hres m)
    obtain ⟨c', rfl⟩ := residue_surjective c
    have hD0 : D hres (m - c' * t) = 0 := by
      have hsub : D hres (m - c' * t) = D hres m - D hres (c' * t) := by
        rw [eq_sub_iff_add_eq, ← D_add, sub_add_cancel]
      rw [hsub, D_mul, (residue_eq_zero_iff t).2 htm, zero_smul, add_zero, hc, sub_self]
    have hmem : m - c' * t ∈ maximalIdeal R :=
      Ideal.sub_mem _ hm (Ideal.mul_mem_left _ _ htm)
    rw [D_of_mem hres hmem] at hD0
    have h2 : m - c' * t ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R) :=
      mem_sup_of_cls_eq_zero hD0
    have h3 : c' * t ∈ Ideal.span {t} := Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
    have : m = c' * t + (m - c' * t) := by ring
    rw [this, sup_assoc]
    exact Submodule.add_mem_sup h3 h2

  have ht : t ∉ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R) := by
    intro hmem
    apply hr₀
    rw [← hΦt]
    exact snd_eq_zero_of_mem_sup hres Φ₁ hΦ₁ hmem
  obtain ⟨e, he⟩ :=
    IsLocalRing.exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map
      hres hsmooth t htm hgen ht
  refine ⟨e, ?_⟩
  rw [he, hΦt]
  exact hr₀

end S_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
end P2MW
export P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber (solution)
