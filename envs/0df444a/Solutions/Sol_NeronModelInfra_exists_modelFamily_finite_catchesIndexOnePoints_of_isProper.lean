-- Prove2me | solution 1 for NeronModelInfra.exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f6c1b49e-d8d6-523b-9314-3b228b8fac4b

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Theorems.Thm_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.NeronModelInfra"

universe u

namespace NeronModelInfra
p2m_export "NeronModelInfra" "pointGenericFibre pointGenericFibre_coe_comp_fst ModelFamily specGenericFibreInclusion SchemeHomOver"
namespace BoundedModels
p2m_open "NeronModelInfra"

open scoped nonZeroDivisors

section Algebra

variable {R : Type u} [CommRing R] [IsDomain R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type u} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

def model (s : Set A) (c : R) : Subalgebra R A :=
  Algebra.adjoin R ((fun g => algebraMap R A c * g) '' s)

omit [IsDomain R] in
theorem model_fg {s : Set A} (hs : s.Finite) (c : R) : (model s c).FG :=
  Subalgebra.fg_def.mpr ⟨_, hs.image _, rfl⟩

omit [IsDomain R] in
theorem finiteType_model {s : Set A} (hs : s.Finite) (c : R) : Algebra.FiniteType R (model s c) :=
  (Subalgebra.fg_iff_finiteType _).mp (model_fg hs c)

omit [IsDomain R] in
theorem mul_mem_model {s : Set A} (c : R) {g : A} (hg : g ∈ s) : algebraMap R A c * g ∈ model s c :=
  Algebra.subset_adjoin ⟨g, hg, rfl⟩

omit [IsDomain R] [IsFractionRing R K] in
theorem algebraMap_isUnit_of_ne_zero [FaithfulSMul R K] {r : R} (hr : r ≠ 0) : IsUnit (algebraMap R A r) := by
  rw [IsScalarTower.algebraMap_apply R K A]
  exact ((FaithfulSMul.algebraMap_injective R K).ne_iff' (map_zero _) |>.mpr hr).isUnit.map _

theorem exists_mul_mem_model {s : Set A} (hs : Algebra.adjoin K s = ⊤) {c : R} (hc : c ≠ 0) (z : A) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R A r * z ∈ model s c := by
  have hz : z ∈ Algebra.adjoin K s := by rw [hs]; exact Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact ⟨c, hc, mul_mem_model c hx⟩
  | algebraMap k =>
    obtain ⟨n, d, hd0, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    refine ⟨d, nonZeroDivisors.ne_zero hd0, ?_⟩
    by_cases hd : algebraMap R K d = 0
    · exact absurd hd (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0)
    · have : algebraMap R A d * algebraMap K A (algebraMap R K n / algebraMap R K d) = algebraMap R A n := by
        rw [IsScalarTower.algebraMap_apply R K A, IsScalarTower.algebraMap_apply R K A, ← map_mul,
          mul_div_cancel₀ _ hd]
      rw [this]
      exact Subalgebra.algebraMap_mem _ n
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : algebraMap R A (r * t) * (x + y) =
        algebraMap R A t * (algebraMap R A r * x) + algebraMap R A r * (algebraMap R A t * y) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ t) hx)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : algebraMap R A (r * t) * (x * y) = (algebraMap R A r * x) * (algebraMap R A t * y) := by
      rw [map_mul]; ring
    rw [this]
    exact Subalgebra.mul_mem _ hx hy

theorem isLocalization_model {s : Set A} (hs : Algebra.adjoin K s = ⊤) {c : R} (hc : c ≠ 0) :
    IsLocalization ((nonZeroDivisors R).map (algebraMap R (model s c))) A where
  map_units := by
    rintro ⟨_, r, hr, rfl⟩
    change IsUnit (algebraMap (model s c) A (algebraMap R (model s c) r))
    rw [← IsScalarTower.algebraMap_apply]
    exact algebraMap_isUnit_of_ne_zero (K := K) (nonZeroDivisors.ne_zero hr)
  surj := by
    intro z
    obtain ⟨r, hr, hz⟩ := exists_mul_mem_model (K := K) hs hc z
    refine ⟨⟨⟨_, hz⟩, ⟨algebraMap R (model s c) r, r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩⟩, ?_⟩
    change z * algebraMap (model s c) A (algebraMap R (model s c) r) = algebraMap R A r * z
    rw [← IsScalarTower.algebraMap_apply, mul_comm]
  exists_of_eq := by
    intro x y h
    exact ⟨1, by rw [Subtype.ext (show (x : A) = y from h)]⟩

include K in

theorem isTorsionFree_model (s : Set A) (c : R) : Module.IsTorsionFree R (model s c) := by
  have hA : Module.IsTorsionFree R A := by
    refine ⟨fun r hr => ?_⟩
    have hr0 : r ≠ 0 := by rintro rfl; exact not_isRegular_zero hr
    intro x y hxy
    have hu := algebraMap_isUnit_of_ne_zero (K := K) (A := A) hr0
    have : algebraMap R A r * x = algebraMap R A r * y := by simpa [Algebra.smul_def] using hxy
    exact hu.mul_left_cancel this
  exact Function.Injective.moduleIsTorsionFree (model s c).val Subtype.val_injective (fun _ _ => rfl)

include K in

theorem flat_model [IsDedekindDomain R] (s : Set A) (c : R) : Module.Flat R (model s c) := by
  have := isTorsionFree_model (K := K) s c
  infer_instance

omit [IsDomain R] in

theorem exists_lift_model {s : Set A} (c : R)
    {R' K' : Type u} [CommRing R'] [CommRing K'] [Algebra R R'] [Algebra R' K'] [Algebra R K']
    [IsScalarTower R R' K'] (hinj : Function.Injective (algebraMap R' K'))
    (ψ : A →ₐ[R] K') (hψ : ∀ g ∈ s, ψ (algebraMap R A c * g) ∈ Set.range (algebraMap R' K')) :
    ∃ χ : model s c →ₐ[R] R', ∀ b : model s c, algebraMap R' K' (χ b) = ψ b := by
  let T : Subalgebra R K' := (IsScalarTower.toAlgHom R R' K').range
  have hle : (model s c).map ψ ≤ T := by
    rw [model, AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hψ g hg
    exact ⟨y, hy⟩
  have hmem : ∀ b : model s c, ψ b ∈ Set.range (algebraMap R' K') := by
    intro b
    obtain ⟨y, hy⟩ := hle ⟨b, b.2, rfl⟩
    exact ⟨y, hy⟩
  choose χ hχ using hmem
  refine ⟨{ toFun := χ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ },
    fun b => hχ b⟩
  · apply hinj; rw [hχ]; simp
  · intro x y; apply hinj; rw [hχ, map_mul, hχ, hχ]; simp
  · apply hinj; rw [hχ]; simp
  · intro x y; apply hinj; rw [hχ, map_add, hχ, hχ]; simp
  · intro r; apply hinj; rw [hχ, ← IsScalarTower.algebraMap_apply]; simp

end Algebra

section Coordinates

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K))

def algK (V : AK.Opens) : K →+* Γ(AK, V) :=
  (gK.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem ofHom_algK (V : AK.Opens) :
    CommRingCat.ofHom (algK K gK V) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ V le_top :=
  rfl

@[nolint unusedArguments]
def Coord (_R K : Type u) [Field K] {AK : Scheme.{u}} (_gK : AK ⟶ Spec (CommRingCat.of K)) (V : AK.Opens) : Type u :=
  Γ(AK, V)

variable (V : AK.Opens)

scoped instance : CommRing (Coord R K gK V) := inferInstanceAs (CommRing Γ(AK, V))

scoped instance : Algebra K (Coord R K gK V) := (algK K gK V).toAlgebra

scoped instance : Algebra R (Coord R K gK V) := ((algK K gK V).comp (algebraMap R K)).toAlgebra

scoped instance : IsScalarTower R K (Coord R K gK V) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem fromSpec_comp_eq {V : AK.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ gK = Spec.map (CommRingCat.ofHom (algK K gK V)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top (Spec (CommRingCat.of K))) hV
    (le_top : V ≤ gK ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h, ofHom_algK]

theorem finiteType_algK [LocallyOfFiniteType gK] {V : AK.Opens} (hV : IsAffineOpen V) :
    (algK K gK V).FiniteType := by
  have h1 : (gK.appLE ⊤ V le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType gK inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  exact h1.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)

variable {K gK}

def evalHom {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ AK) (V : AK.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ V) : Γ(AK, V) →+* L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp (a.appLE V ⊤ h).hom

theorem ofHom_evalHom {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ AK) (V : AK.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ V) :
    CommRingCat.ofHom (evalHom a V h) = a.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom :=
  rfl

theorem evalHom_apply {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ AK) (V : AK.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ V) (g : Γ(AK, V)) :
    evalHom a V h g = (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE V ⊤ h g) :=
  rfl

theorem evalHom_comp_algK {L : Type u} [CommRing L] [Algebra K L] (a : Spec (CommRingCat.of L) ⟶ AK)
    (ha : a ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K L))) (V : AK.Opens) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    (evalHom a V h).comp (algK K gK V) = algebraMap K L := by
  have h1 : gK.appLE ⊤ V le_top ≫ a.appLE V ⊤ h = (Spec.map (CommRingCat.ofHom (algebraMap K L))).appTop := by
    rw [Scheme.Hom.appLE_comp_appLE, ← ha]
    exact Scheme.Hom.appLE_eq_app _
  have h2 : CommRingCat.ofHom ((evalHom a V h).comp (algK K gK V)) = CommRingCat.ofHom (algebraMap K L) := by
    rw [CommRingCat.ofHom_comp, ofHom_evalHom, ofHom_algK, Category.assoc,
      reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom h2

theorem eq_specMap_evalHom_comp_fromSpec {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ AK)
    {V : AK.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    a = Spec.map (CommRingCat.ofHom (evalHom a V h)) ≫ hV.fromSpec := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec a hV (isAffineOpen_top (Spec (CommRingCat.of L))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  rw [ofHom_evalHom, Spec.map_comp, Category.assoc, h1, ← Spec.map_comp_assoc, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem top_le_preimage_of_mem {L : Type u} [CommRing L] [IsLocalRing L] (a : Spec (CommRingCat.of L) ⟶ AK)
    {V : AK.Opens} (h : a.base (IsLocalRing.closedPoint L) ∈ V) : ⊤ ≤ a ⁻¹ᵁ V := by
  rintro x -
  change a.base x ∈ V
  exact ((IsLocalRing.specializes_closedPoint x).map a.base.hom.continuous).mem_open V.2 h

end Coordinates

section Family

variable {R : Type u} [CommRing R] [IsDomain R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K))
variable {ι : Type u} (U : ι → AK.Opens) (s : ∀ i, Finset Γ(AK, U i)) (c : R)

variable (R) in

def gens (i : ι) : Set (Coord R K gK (U i)) := ((s i : Set Γ(AK, U i)) : Set Γ(AK, U i))

omit [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] in
variable (R) in
theorem mem_gens_iff (i : ι) (g : Γ(AK, U i)) : (g : Coord R K gK (U i)) ∈ gens R K gK U s i ↔ g ∈ s i :=
  Finset.mem_coe

def modelRing (i : ι) : Subalgebra R (Coord R K gK (U i)) :=
  model (A := Coord R K gK (U i)) (gens R K gK U s i) c

def memberX (i : ι) : Scheme.{u} := Spec (CommRingCat.of (modelRing K gK U s c i))

def memberStr (i : ι) : memberX K gK U s c i ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (modelRing K gK U s c i)))

def coordToMember (i : ι) : Spec Γ(AK, U i) ⟶ memberX K gK U s c i :=
  Spec.map (CommRingCat.ofHom (algebraMap (modelRing K gK U s c i) (Coord R K gK (U i))))

def coordStr (i : ι) : Spec Γ(AK, U i) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algK K gK (U i)))

variable {K gK U s c}

theorem isPullback_member (hs : ∀ i, Algebra.adjoin K (gens R K gK U s i) = ⊤)
    (hc : c ≠ 0) (i : ι) :
    IsPullback (coordToMember K gK U s c i) (coordStr K gK U i)
      (memberStr K gK U s c i) (specGenericFibreInclusion R K) := by
  have : IsLocalization ((nonZeroDivisors R).map (algebraMap R (modelRing K gK U s c i)))
      (Coord R K gK (U i)) := isLocalization_model (K := K) (hs i) hc
  have H : (algebraMap K (Coord R K gK (U i))).comp (algebraMap R K) =
      (algebraMap (modelRing K gK U s c i) (Coord R K gK (U i))).comp
        (algebraMap R (modelRing K gK U s c i)) := by
    ext r
    exact (IsScalarTower.algebraMap_apply R (modelRing K gK U s c i) (Coord R K gK (U i)) r)
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap R (modelRing K gK U s c i))
      (algebraMap K (Coord R K gK (U i))) H (nonZeroDivisors R))

theorem mono_coordToMember (hs : ∀ i, Algebra.adjoin K (gens R K gK U s i) = ⊤)
    (hc : c ≠ 0) (i : ι) : Mono (coordToMember K gK U s c i) := by
  have : IsLocalization ((nonZeroDivisors R).map (algebraMap R (modelRing K gK U s c i)))
      (Coord R K gK (U i)) := isLocalization_model (K := K) (hs i) hc
  have : IsPreimmersion (coordToMember K gK U s c i) :=
    IsPreimmersion.of_isLocalization (S := Coord R K gK (U i))
      ((nonZeroDivisors R).map (algebraMap R (modelRing K gK U s c i)))
  infer_instance

variable (hU : ∀ i, IsAffineOpen (U i))
variable (hs : ∀ i, Algebra.adjoin K (gens R K gK U s i) = ⊤) (hc : c ≠ 0)

def memberChart (i : ι) :
    SchemeHomOver (pullback.snd (memberStr K gK U s c i) (specGenericFibreInclusion R K)) gK :=
  ⟨(isPullback_member hs hc i).isoPullback.inv ≫ (hU i).fromSpec, by
    rw [Category.assoc, fromSpec_comp_eq K gK (hU i)]
    exact (isPullback_member hs hc i).isoPullback_inv_snd⟩

omit [IsDomain R] [IsFractionRing R K] in
theorem coordStr_eq (i : ι) : Spec.map (CommRingCat.ofHom (algK K gK (U i))) = coordStr K gK U i := rfl

scoped instance isOpenImmersion_memberChart (i : ι) : IsOpenImmersion (memberChart hU hs hc i).1 := by
  change IsOpenImmersion ((isPullback_member hs hc i).isoPullback.inv ≫ (hU i).fromSpec)
  infer_instance

def family : ModelFamily R K gK where
  ι := ι
  X := memberX K gK U s c
  str := memberStr K gK U s c
  chart := memberChart hU hs hc
  isOpenImmersion_chart := isOpenImmersion_memberChart hU hs hc

omit [IsDomain R] [IsFractionRing R K] in
theorem isAffine_memberX (i : ι) : IsAffine (memberX K gK U s c i) := by
  delta memberX; infer_instance

theorem flat_memberStr [IsDedekindDomain R] (i : ι) : Flat (memberStr K gK U s c i) := by
  have := flat_model (K := K) (A := Coord R K gK (U i)) (gens R K gK U s i) c
  delta memberStr
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr this)

omit [IsDomain R] [IsFractionRing R K] in
theorem locallyOfFiniteType_memberStr (i : ι) : LocallyOfFiniteType (memberStr K gK U s c i) := by
  have := finiteType_model (A := Coord R K gK (U i)) (s := gens R K gK U s i) (s i).finite_toSet c
  delta memberStr
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr this)

theorem catchesIndexOnePoints_family [IsLocalRing R]
    (hbd : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
        (L : Type u) [Field L] [Algebra V L] [IsFractionRing V L] [Algebra R L] [IsScalarTower R V L]
        [Algebra K L] [IsScalarTower R K L]
        (a : Spec (CommRingCat.of L) ⟶ AK), a ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K L)) →
        ∃ (i : ι) (h : ⊤ ≤ a ⁻¹ᵁ U i), ∀ g ∈ s i,
          algebraMap R L c * (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE (U i) ⊤ h g) ∈
            Set.range (algebraMap V L)) :
    (family hU hs hc).CatchesIndexOnePoints := by
  intro R' _ _ _ _ _ K' _ _ _ _ _ _ _ _ a
  obtain ⟨i, h, hg⟩ := hbd R' K' a.1 a.2

  let A := Coord R K gK (U i)
  let ψr : A →+* K' := evalHom a.1 (U i) h
  have hψK : ψr.comp (algK K gK (U i)) = algebraMap K K' := evalHom_comp_algK a.1 a.2 (U i) h
  have hψR : ∀ r : R, ψr (algebraMap R A r) = algebraMap R K' r := fun r =>
    calc ψr (algebraMap R A r) = (ψr.comp (algK K gK (U i))) (algebraMap R K r) := rfl
      _ = algebraMap K K' (algebraMap R K r) := by rw [hψK]
      _ = algebraMap R K' r := (IsScalarTower.algebraMap_apply R K K' r).symm
  let ψ : A →ₐ[R] K' := { ψr with commutes' := hψR }
  have hψ : ∀ g ∈ gens R K gK U s i, ψ (algebraMap R A c * g) ∈ Set.range (algebraMap R' K') := by
    intro g hgs
    have := hg g ((mem_gens_iff R K gK U s i g).mp hgs)
    rwa [map_mul, show ψ (algebraMap R A c) = algebraMap R K' c from hψR c]
  obtain ⟨χ, hχ⟩ := exists_lift_model c (IsFractionRing.injective R' K') ψ hψ

  have hχR : (χ.toRingHom : modelRing K gK U s c i →+* R').comp (algebraMap R (modelRing K gK U s c i)) =
      algebraMap R R' :=
    χ.comp_algebraMap
  refine ⟨i, ⟨Spec.map (CommRingCat.ofHom (χ.toRingHom : modelRing K gK U s c i →+* R')), ?_⟩, ?_⟩
  · change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ : R →+* R' => Spec.map (CommRingCat.ofHom φ)) hχR
  · apply Subtype.ext
    change (pointGenericFibre _).1 ≫ (isPullback_member hs hc i).isoPullback.inv ≫ (hU i).fromSpec = a.1
    rw [eq_specMap_evalHom_comp_fromSpec a.1 (hU i) h, ← Category.assoc]
    congr 1
    haveI := mono_coordToMember hs hc i
    rw [← cancel_mono (coordToMember K gK U s c i), Category.assoc,
      (isPullback_member hs hc i).isoPullback_inv_fst]
    rw [pointGenericFibre_coe_comp_fst]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext b
    exact hχ b

end Family

end NeronModelInfra.BoundedModels
p2m_reactivate "P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.NeronModelInfra P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.NeronModelInfra.BoundedModels"
p2m_reactivate "P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.NeronModelInfra"

open NeronModelInfra.BoundedModels in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) [IsProper gK] :
    ∃ M : ModelFamily R K gK, Finite M.ι ∧
      (∀ i, IsAffine (M.X i) ∧ IsSeparated (M.str i) ∧ Flat (M.str i) ∧
        LocallyOfFiniteType (M.str i) ∧ QuasiCompact (M.str i)) ∧
      M.CatchesIndexOnePoints := by

  haveI : CompactSpace AK := QuasiCompact.compactSpace_of_compactSpace gK
  let 𝒱 := AK.affineCover.finiteSubcover
  let U : 𝒱.I₀ → AK.Opens := fun j => (𝒱.f j).opensRange
  have hU : ∀ j, IsAffineOpen (U j) := fun j => isAffineOpen_opensRange (𝒱.f j)
  have hcov : ⨆ j, U j = ⊤ := 𝒱.iSup_opensRange

  have hgen : ∀ j, ∃ t : Finset (Coord R K gK (U j)), Algebra.adjoin K (t : Set (Coord R K gK (U j))) = ⊤ := by
    intro j
    have hft : Algebra.FiniteType K (Coord R K gK (U j)) := finiteType_algK K gK (hU j)
    exact hft.out
  choose s hs using hgen

  obtain ⟨c, hc, hbd⟩ :=
    AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper (R := R) K gK U
      hcov s

  have hs' : ∀ j, Algebra.adjoin K (gens R K gK U s j) = ⊤ := fun j => hs j
  refine ⟨family hU hs' hc, ?_, ?_, catchesIndexOnePoints_family hU hs' hc hbd⟩
  · change Finite 𝒱.I₀
    infer_instance
  · intro j
    refine ⟨isAffine_memberX j, ?_, flat_memberStr j, locallyOfFiniteType_memberStr j, ?_⟩
    · change IsSeparated (Spec.map _)
      infer_instance
    · change QuasiCompact (Spec.map _)
      infer_instance

end
p2m_reactivate "P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.NeronModelInfra P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.NeronModelInfra.BoundedModels"

end S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
end P2MW
export P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper (solution)
