-- Prove2me | solution 1 for IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5ec0cb15-a480-5daa-95f4-7afcd52cd941

import Mathlib
import Theorems.Thm_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
import Theorems.Thm_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open IsLocalRing Polynomial

namespace P2mResidueExtension

section Setup

variable (T : Type u) [CommRing T] [IsLocalRing T]
variable (K : Type u) [Field K] [Algebra (ResidueField T) K]

@[reducible] noncomputable def algTK : Algebra T K :=
  ((algebraMap (ResidueField T) K).comp (residue T)).toAlgebra

attribute [local instance] algTK

theorem algebraMap_TK_apply (t : T) :
    algebraMap T K t = algebraMap (ResidueField T) K (residue T t) := rfl

scoped instance isScalarTower_TK : IsScalarTower T (ResidueField T) K :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable [LinearOrder K]

variable {K} in

def S (x : WithTop K) : Set K := {b | (b : WithTop K) < x}

variable {T K}

theorem mem_S {x : WithTop K} {b : K} : b ∈ S x ↔ (b : WithTop K) < x := Iff.rfl

theorem S_mono {y x : WithTop K} (h : y ≤ x) : S y ⊆ S x := fun _ hb => lt_of_lt_of_le hb h

def incl {y x : WithTop K} (h : y ≤ x) : S y → S x := Set.inclusion (S_mono h)

@[scoped simp] theorem coe_incl {y x : WithTop K} (h : y ≤ x) (c : S y) : ((incl h c : S x) : K) = c := rfl

theorem incl_injective {y x : WithTop K} (h : y ≤ x) : Function.Injective (incl h) :=
  Set.inclusion_injective (S_mono h)

variable (T)

abbrev P (x : WithTop K) : Type u := MvPolynomial (S x) T

noncomputable def ρ {y x : WithTop K} (h : y ≤ x) : P T y →ₐ[T] P T x := MvPolynomial.rename (incl h)

noncomputable def ψ0 (x : WithTop K) : P T x →ₐ[T] K := MvPolynomial.aeval (fun s : S x => (s : K))

variable {T}

@[scoped simp] theorem ρ_X {y x : WithTop K} (h : y ≤ x) (c : S y) :
    ρ T h (MvPolynomial.X c) = MvPolynomial.X (incl h c) := by
  simp [ρ]

@[scoped simp] theorem ψ0_X {x : WithTop K} (c : S x) : ψ0 T x (MvPolynomial.X c) = (c : K) := by
  simp [ψ0]

theorem ρ_comp_ρ {z y x : WithTop K} (h₁ : z ≤ y) (h₂ : y ≤ x) :
    (ρ T h₂).comp (ρ T h₁) = ρ T (h₁.trans h₂) := by
  apply MvPolynomial.algHom_ext
  intro c
  simp only [AlgHom.comp_apply, ρ_X]
  rfl

theorem ρ_ρ {z y x : WithTop K} (h₁ : z ≤ y) (h₂ : y ≤ x) (p : P T z) :
    ρ T h₂ (ρ T h₁ p) = ρ T (h₁.trans h₂) p := by
  rw [← AlgHom.comp_apply, ρ_comp_ρ]

theorem ρ_refl (x : WithTop K) : ρ T (le_refl x) = AlgHom.id T (P T x) := by
  apply MvPolynomial.algHom_ext
  intro c
  simp only [ρ_X, AlgHom.id_apply]
  rfl

theorem ρ_injective {y x : WithTop K} (h : y ≤ x) : Function.Injective (ρ T h) :=
  MvPolynomial.rename_injective _ (incl_injective h)

theorem ψ0_comp_ρ {y x : WithTop K} (h : y ≤ x) : (ψ0 T x).comp (ρ T h) = ψ0 T y := by
  apply MvPolynomial.algHom_ext
  intro c
  simp

theorem ψ0_ρ {y x : WithTop K} (h : y ≤ x) (p : P T y) : ψ0 T x (ρ T h p) = ψ0 T y p := by
  rw [← AlgHom.comp_apply, ψ0_comp_ρ]

theorem comap_map_ρ {y x : WithTop K} (h : y ≤ x) (I : Ideal (P T y)) :
    (I.map (ρ T h)).comap (ρ T h) = I := by
  refine le_antisymm ?_ (Ideal.le_comap_map)
  intro p hp
  have hle : I.map (ρ T h) ≤ I.comap (MvPolynomial.killCompl (incl_injective h)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    simpa [Ideal.mem_comap, ρ] using hq
  have h2 := hle hp
  simpa [Ideal.mem_comap, ρ] using h2

variable (T) in

noncomputable abbrev E (x : WithTop K) : IntermediateField (ResidueField T) K :=
  IntermediateField.adjoin (ResidueField T) (S x)

theorem mem_adjoinT_iff (s : Set K) (z : K) :
    z ∈ Algebra.adjoin T s ↔ z ∈ Algebra.adjoin (ResidueField T) s := by
  constructor
  · intro hz
    have hle : Algebra.adjoin T s ≤ (Algebra.adjoin (ResidueField T) s).restrictScalars T := by
      rw [Algebra.adjoin_le_iff]
      intro w hw
      rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
      exact Algebra.subset_adjoin hw
    exact (Subalgebra.mem_restrictScalars T).mp (hle hz)
  · intro hz
    induction hz using Algebra.adjoin_induction with
    | mem w hw => exact Algebra.subset_adjoin hw
    | algebraMap c =>
        obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective c
        rw [← algebraMap_TK_apply]
        exact Subalgebra.algebraMap_mem _ t
    | add a b _ _ ha hb => exact Subalgebra.add_mem _ ha hb
    | mul a b _ _ ha hb => exact Subalgebra.mul_mem _ ha hb

variable [Algebra.IsAlgebraic (ResidueField T) K]

theorem mem_range_ψ0_iff (x : WithTop K) (z : K) : z ∈ (ψ0 T x).range ↔ z ∈ E T x := by
  have hr : (ψ0 T x).range = Algebra.adjoin T (S x) := by
    rw [ψ0, ← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe]
  rw [hr, mem_adjoinT_iff, ← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra]

noncomputable abbrev F (a : K) : Polynomial (E T (a : WithTop K)) := minpoly (E T (a : WithTop K)) a

theorem isIntegral_E (a : K) : IsIntegral (E T (a : WithTop K)) a :=
  (Algebra.IsIntegral.isIntegral (R := ResidueField T) a).tower_top

theorem F_irreducible (a : K) : Irreducible (F (T := T) a) := minpoly.irreducible (isIntegral_E a)

theorem F_monic (a : K) : (F (T := T) a).Monic := minpoly.monic (isIntegral_E a)

theorem exists_G (a : K) : ∃ G : Polynomial (P T (a : WithTop K)), G.Monic ∧
    G.map (ψ0 T (a : WithTop K) : P T (a : WithTop K) →+* K) = (F a).map (algebraMap (E T (a : WithTop K)) K) := by
  have hl : (F a).map (algebraMap (E T (a : WithTop K)) K) ∈
      Polynomial.lifts (ψ0 T (a : WithTop K) : P T (a : WithTop K) →+* K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    have hmem : (algebraMap (E T (a : WithTop K)) K) ((F a).coeff n) ∈ (ψ0 T (a : WithTop K)).range := by
      rw [mem_range_ψ0_iff]
      exact ((F a).coeff n).2
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  obtain ⟨G, hG, -, hGm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl ((F_monic a).map _)
  exact ⟨G, hGm, hG⟩

noncomputable def G (a : K) : Polynomial (P T (a : WithTop K)) := (exists_G (T := T) a).choose

theorem G_monic (a : K) : (G (T := T) a).Monic := (exists_G (T := T) a).choose_spec.1

theorem G_map (a : K) :
    (G (T := T) a).map (ψ0 T (a : WithTop K) : P T (a : WithTop K) →+* K) = (F a).map (algebraMap (E T (a : WithTop K)) K) :=
  (exists_G (T := T) a).choose_spec.2

theorem natDegree_G_pos (a : K) : 0 < (G (T := T) a).natDegree := by
  have h1 : (G (T := T) a).natDegree = ((G (T := T) a).map (ψ0 T (a : WithTop K) : P T (a : WithTop K) →+* K)).natDegree :=
    ((G_monic a).natDegree_map _).symm
  rw [h1, G_map, (F_monic a).natDegree_map]
  exact minpoly.natDegree_pos (isIntegral_E a)

variable (T) in

noncomputable def gen (x : WithTop K) (c : S x) : P T x :=
  ((G (T := T) (c : K)).map (ρ T (le_of_lt c.2) : P T _ →+* P T x)).eval (MvPolynomial.X c)

theorem gen_eq (x : WithTop K) (c : S x) (h : ((c : K) : WithTop K) ≤ x) :
    gen T x c = (G (T := T) (c : K)).eval₂ (ρ T h : P T _ →+* P T x) (MvPolynomial.X c) := by
  rw [gen, Polynomial.eval_map]

theorem ρ_gen {y x : WithTop K} (h : y ≤ x) (c : S y) : ρ T h (gen T y c) = gen T x (incl h c) := by
  rw [gen_eq y c (le_of_lt c.2), gen_eq x (incl h c) (le_of_lt (incl h c).2)]
  change (ρ T h : P T y →+* P T x) (Polynomial.eval₂ _ _ _) = _
  rw [Polynomial.hom_eval₂, ← AlgHom.comp_toRingHom, ρ_comp_ρ, AlgHom.coe_toRingHom, ρ_X]
  rfl

theorem ψ0_gen (x : WithTop K) (c : S x) : ψ0 T x (gen T x c) = 0 := by
  rw [gen_eq x c (le_of_lt c.2)]
  change (ψ0 T x : P T x →+* K) (Polynomial.eval₂ _ _ _) = _
  rw [Polynomial.hom_eval₂, ← AlgHom.comp_toRingHom, ψ0_comp_ρ, AlgHom.coe_toRingHom, ψ0_X,
    ← Polynomial.eval_map, G_map, Polynomial.eval_map, ← Polynomial.aeval_def]
  exact minpoly.aeval _ _

variable (T) in

noncomputable def 𝔔 (x : WithTop K) : Ideal (P T x) := Ideal.span (Set.range (gen T x))

theorem gen_mem_𝔔 (x : WithTop K) (c : S x) : gen T x c ∈ 𝔔 T x := Ideal.subset_span ⟨c, rfl⟩

theorem 𝔔_map_le {y x : WithTop K} (h : y ≤ x) : (𝔔 T y).map (ρ T h) ≤ 𝔔 T x := by
  rw [𝔔, Ideal.map_span]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  rw [ρ_gen]
  exact gen_mem_𝔔 x _

theorem 𝔔_le_comap {y x : WithTop K} (h : y ≤ x) : 𝔔 T y ≤ (𝔔 T x).comap (ρ T h) :=
  Ideal.map_le_iff_le_comap.mp (𝔔_map_le h)

theorem 𝔔_le_ker (x : WithTop K) : ∀ p ∈ 𝔔 T x, ψ0 T x p = 0 := by
  intro p hp
  have : 𝔔 T x ≤ RingHom.ker (ψ0 T x) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨c, rfl⟩
    exact ψ0_gen x c
  exact this hp

variable (T) in

abbrev B (x : WithTop K) : Type u := P T x ⧸ 𝔔 T x

variable (T) in

private noncomputable def _root_.P2mResidueExtension.mk (x : WithTop K) : P T x →ₐ[T] B T x := Ideal.Quotient.mkₐ T (𝔔 T x)

p2m_export "P2mResidueExtension" "mk"
theorem mk_apply (x : WithTop K) (p : P T x) : mk T x p = Ideal.Quotient.mk (𝔔 T x) p := rfl

private theorem _root_.P2mResidueExtension.mk_surjective (x : WithTop K) : Function.Surjective (mk T x) := Ideal.Quotient.mk_surjective

p2m_export "P2mResidueExtension" "mk_surjective"
theorem mk_gen (x : WithTop K) (c : S x) : mk T x (gen T x c) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (gen_mem_𝔔 x c)

variable (T) in

noncomputable def ψ (x : WithTop K) : B T x →ₐ[T] K := Ideal.Quotient.liftₐ (𝔔 T x) (ψ0 T x) (𝔔_le_ker x)

@[scoped simp] theorem ψ_mk (x : WithTop K) (p : P T x) : ψ T x (mk T x p) = ψ0 T x p := rfl

variable (T) in

noncomputable def φ {y x : WithTop K} (h : y ≤ x) : B T y →ₐ[T] B T x :=
  Ideal.quotientMapₐ (𝔔 T x) (ρ T h) (𝔔_le_comap h)

@[scoped simp] theorem φ_mk {y x : WithTop K} (h : y ≤ x) (p : P T y) : φ T h (mk T y p) = mk T x (ρ T h p) := rfl

theorem φ_comp_φ {z y x : WithTop K} (h₁ : z ≤ y) (h₂ : y ≤ x) :
    (φ T h₂).comp (φ T h₁) = φ T (h₁.trans h₂) := by
  refine Ideal.Quotient.algHom_ext T ?_
  apply MvPolynomial.algHom_ext
  intro c
  change φ T h₂ (φ T h₁ (mk T z (MvPolynomial.X c))) = φ T (h₁.trans h₂) (mk T z (MvPolynomial.X c))
  simp only [φ_mk, ρ_ρ]

theorem φ_φ {z y x : WithTop K} (h₁ : z ≤ y) (h₂ : y ≤ x) (b : B T z) :
    φ T h₂ (φ T h₁ b) = φ T (h₁.trans h₂) b := by
  rw [← AlgHom.comp_apply, φ_comp_φ]

theorem φ_refl (x : WithTop K) : φ T (le_refl x) = AlgHom.id T (B T x) := by
  refine Ideal.Quotient.algHom_ext T ?_
  apply MvPolynomial.algHom_ext
  intro c
  change φ T (le_refl x) (mk T x (MvPolynomial.X c)) = mk T x (MvPolynomial.X c)
  rw [φ_mk, ρ_refl, AlgHom.id_apply]

theorem φ_refl_apply (x : WithTop K) (h : x ≤ x) (b : B T x) : φ T h b = b := by
  rw [show φ T h = φ T (le_refl x) from rfl, φ_refl, AlgHom.id_apply]

theorem ψ_comp_φ {y x : WithTop K} (h : y ≤ x) : (ψ T x).comp (φ T h) = ψ T y := by
  refine Ideal.Quotient.algHom_ext T ?_
  apply MvPolynomial.algHom_ext
  intro c
  change ψ T x (φ T h (mk T y (MvPolynomial.X c))) = ψ T y (mk T y (MvPolynomial.X c))
  rw [φ_mk, ψ_mk, ψ_mk, ψ0_ρ]

theorem ψ_φ {y x : WithTop K} (h : y ≤ x) (b : B T y) : ψ T x (φ T h b) = ψ T y b := by
  rw [← AlgHom.comp_apply, ψ_comp_φ]

theorem algebraMap_B (x : WithTop K) (t : T) : algebraMap T (B T x) t = mk T x (MvPolynomial.C t) := rfl

theorem φ_comp_algebraMap {y x : WithTop K} (h : y ≤ x) :
    (φ T h).toRingHom.comp (algebraMap T (B T y)) = algebraMap T (B T x) :=
  (φ T h).comp_algebraMap

theorem ψ_algebraMap (x : WithTop K) (t : T) : ψ T x (algebraMap T (B T x) t) = algebraMap T K t :=
  (ψ T x).commutes t

theorem ψ_mem_E (x : WithTop K) (b : B T x) : ψ T x b ∈ E T x := by
  obtain ⟨p, rfl⟩ := mk_surjective x b
  rw [ψ_mk, ← mem_range_ψ0_iff]
  exact ⟨p, rfl⟩

variable (T) in

noncomputable def ψL (x : WithTop K) : B T x →+* E T x :=
  (ψ T x).toRingHom.codRestrict (E T x) (ψ_mem_E x)

theorem coe_ψL (x : WithTop K) (b : B T x) : (ψL T x b : K) = ψ T x b := rfl

theorem ψL_surjective (x : WithTop K) : Function.Surjective (ψL T x) := by
  intro z
  have hz : (z : K) ∈ (ψ0 T x).range := (mem_range_ψ0_iff x z).mpr z.2
  obtain ⟨p, hp⟩ := hz
  exact ⟨mk T x p, Subtype.ext (by rw [coe_ψL, ψ_mk]; exact hp)⟩

theorem ker_ψL (x : WithTop K) : RingHom.ker (ψL T x) = RingHom.ker (ψ T x : B T x →+* K) := by
  ext b
  simp only [RingHom.mem_ker]
  rw [← Subtype.coe_inj, coe_ψL]
  rfl

theorem ker_ψ_eq_maximalIdeal (x : WithTop K) [IsLocalRing (B T x)] :
    RingHom.ker (ψ T x : B T x →+* K) = maximalIdeal (B T x) := by
  rw [← ker_ψL, IsLocalRing.ker_eq_maximalIdeal (ψL T x) (ψL_surjective x)]

theorem isLocalHom_ψL (x : WithTop K) [IsLocalRing (B T x)] : IsLocalHom (ψL T x) := by
  refine ⟨fun b hb => ?_⟩
  by_contra hnu
  have hmem : b ∈ maximalIdeal (B T x) := (IsLocalRing.mem_maximalIdeal b).2 hnu
  rw [← ker_ψ_eq_maximalIdeal, ← ker_ψL, RingHom.mem_ker] at hmem
  rw [hmem] at hb
  exact not_isUnit_zero hb

noncomputable def resEquiv (x : WithTop K) [IsLocalRing (B T x)] : ResidueField (B T x) ≃+* E T x :=
  haveI := isLocalHom_ψL (T := T) x
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (ψL T x))
    ⟨(IsLocalRing.ResidueField.lift (ψL T x)).injective, fun z => by
      obtain ⟨b, rfl⟩ := ψL_surjective x z
      exact ⟨residue (B T x) b, IsLocalRing.ResidueField.lift_residue_apply _ _⟩⟩

theorem resEquiv_residue (x : WithTop K) [IsLocalRing (B T x)] (b : B T x) :
    resEquiv x (residue (B T x) b) = ψL T x b := by
  haveI := isLocalHom_ψL (T := T) x
  exact IsLocalRing.ResidueField.lift_residue_apply _ _

theorem φr_comp {z y x : WithTop K} (h₁ : z ≤ y) (h₂ : y ≤ x) :
    (φ T h₂ : B T y →+* B T x).comp (φ T h₁ : B T z →+* B T y) = (φ T (h₁.trans h₂) : B T z →+* B T x) := by
  rw [← AlgHom.comp_toRingHom, φ_comp_φ]

theorem φr_refl (x : WithTop K) (h : x ≤ x) : (φ T h : B T x →+* B T x) = RingHom.id (B T x) := by
  rw [show φ T h = φ T (le_refl x) from rfl, φ_refl]
  rfl

theorem ψr_comp_φr {y x : WithTop K} (h : y ≤ x) :
    (ψ T x : B T x →+* K).comp (φ T h : B T y →+* B T x) = (ψ T y : B T y →+* K) := by
  rw [← AlgHom.comp_toRingHom, ψ_comp_φ]

theorem φr_comp_algebraMap {y x : WithTop K} (h : y ≤ x) :
    (φ T h : B T y →+* B T x).comp (algebraMap T (B T y)) = algebraMap T (B T x) :=
  (φ T h).comp_algebraMap

theorem map_φ_ker_le {y x : WithTop K} (h : y ≤ x) :
    Ideal.map (φ T h : B T y →+* B T x) (RingHom.ker (ψ T y : B T y →+* K)) ≤
      RingHom.ker (ψ T x : B T x →+* K) := by
  rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, ψr_comp_φr]

theorem comap_algebraMap_ker (x : WithTop K) :
    (RingHom.ker (ψ T x : B T x →+* K)).comap (algebraMap T (B T x)) = maximalIdeal T := by
  ext t
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.coe_toRingHom, ψ_algebraMap, algebraMap_TK_apply,
    map_eq_zero_iff _ (algebraMap (ResidueField T) K).injective, IsLocalRing.residue_eq_zero_iff]

theorem map_algebraMap_maximalIdeal_le (x : WithTop K) :
    Ideal.map (algebraMap T (B T x)) (maximalIdeal T) ≤ RingHom.ker (ψ T x : B T x →+* K) := by
  rw [Ideal.map_le_iff_le_comap, comap_algebraMap_ker]

variable (T) in

structure Good (x : WithTop K) : Prop where
  isLocalRing : IsLocalRing (B T x)
  isNoetherianRing : IsNoetherianRing (B T x)
  flatT : Module.Flat T (B T x)
  mapT : Ideal.map (algebraMap T (B T x)) (maximalIdeal T) = RingHom.ker (ψ T x : B T x →+* K)
  flat : ∀ (y : WithTop K) (h : y ≤ x), (φ T h : B T y →+* B T x).Flat
  inj : ∀ (y : WithTop K) (h : y ≤ x), Function.Injective (φ T h)
  map : ∀ (y : WithTop K) (h : y ≤ x),
    Ideal.map (φ T h : B T y →+* B T x) (RingHom.ker (ψ T y : B T y →+* K)) = RingHom.ker (ψ T x : B T x →+* K)

theorem refl_clauses (x : WithTop K) (h : x ≤ x) :
    (φ T h : B T x →+* B T x).Flat ∧ Function.Injective (φ T h) ∧
      Ideal.map (φ T h : B T x →+* B T x) (RingHom.ker (ψ T x : B T x →+* K)) =
        RingHom.ker (ψ T x : B T x →+* K) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [φr_refl]; exact RingHom.Flat.id _
  · intro a b hab
    rwa [φ_refl_apply, φ_refl_apply] at hab
  · rw [φr_refl, Ideal.map_id]

variable [IsNoetherianRing T]

theorem good_bot (x : WithTop K) (hx : ∀ y, ¬ y < x) : Good T x := by
  haveI : IsEmpty (S x) := ⟨fun c => hx _ c.2⟩
  have h𝔔 : 𝔔 T x = ⊥ := by
    rw [𝔔, Set.range_eq_empty, Ideal.span_empty]
  have hsurj : Function.Surjective (algebraMap T (B T x)) := by
    intro b
    obtain ⟨p, rfl⟩ := mk_surjective x b
    refine ⟨p.coeff 0, ?_⟩
    rw [algebraMap_B]
    exact congrArg (mk T x) (MvPolynomial.eq_C_of_isEmpty p).symm
  have hinj : Function.Injective (algebraMap T (B T x)) := by
    intro t₁ t₂ h
    rw [algebraMap_B, algebraMap_B, mk_apply, mk_apply, Ideal.Quotient.eq, h𝔔, Ideal.mem_bot, ← map_sub,
      MvPolynomial.C_eq_zero, sub_eq_zero] at h
    exact h
  let e : T ≃+* B T x := RingEquiv.ofBijective (algebraMap T (B T x)) ⟨hinj, hsurj⟩
  haveI hloc : IsLocalRing (B T x) := e.isLocalRing
  have hker : Ideal.map (algebraMap T (B T x)) (maximalIdeal T) = RingHom.ker (ψ T x : B T x →+* K) := by
    rw [← comap_algebraMap_ker x, Ideal.map_comap_of_surjective _ hsurj]
  refine ⟨hloc, isNoetherianRing_of_ringEquiv T e, ?_, hker, ?_, ?_, ?_⟩
  · exact RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective ⟨hinj, hsurj⟩)
  · intro y h
    obtain rfl : y = x := h.eq_of_not_lt (hx y)
    exact (refl_clauses y h).1
  · intro y h
    obtain rfl : y = x := h.eq_of_not_lt (hx y)
    exact (refl_clauses y h).2.1
  · intro y h
    obtain rfl : y = x := h.eq_of_not_lt (hx y)
    exact (refl_clauses y h).2.2

theorem mkr_eq (x : WithTop K) : (mk T x : P T x →+* B T x) = Ideal.Quotient.mk (𝔔 T x) := rfl

theorem φr_comp_mkr {y x : WithTop K} (h : y ≤ x) :
    (φ T h : B T y →+* B T x).comp (mk T y : P T y →+* B T y) = (mk T x : P T x →+* B T x).comp (ρ T h) :=
  RingHom.ext fun p => φ_mk h p

theorem ρr_refl (x : WithTop K) (h : x ≤ x) : (ρ T h : P T x →+* P T x) = RingHom.id (P T x) := by
  rw [show ρ T h = ρ T (le_refl x) from rfl, ρ_refl]
  rfl

section Succ

theorem lt_of_mem_S_of_ne {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (c : S x) (hc : (c : K) ≠ a) :
    ((c : K) : WithTop K) < a := by
  by_contra hnot
  have h1 : (a : WithTop K) ≤ c := not_lt.mp hnot
  have h2 : (a : WithTop K) ≠ c := fun h => hc (WithTop.coe_injective h).symm
  exact hax.2 (lt_of_le_of_ne h1 h2) c.2

private theorem _root_.P2mResidueExtension.eq_of_not_lt {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (c : S x)
    (hc : ¬ ((c : K) : WithTop K) < a) : c = ⟨a, hax.lt⟩ := by
  by_contra hne
  exact hc (lt_of_mem_S_of_ne a hax c fun h => hne (Subtype.ext h))

p2m_export "P2mResidueExtension" "eq_of_not_lt"
theorem le_of_lt_of_covBy {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) {y : WithTop K} (hy : y < x) :
    y ≤ a :=
  le_of_not_gt fun h' => hax.2 h' hy

noncomputable def Ghat (a : K) : Polynomial (B T (a : WithTop K)) :=
  (G (T := T) a).map (mk T (a : WithTop K) : P T (a : WithTop K) →+* B T (a : WithTop K))

theorem Ghat_monic (a : K) : (Ghat (T := T) a).Monic := (G_monic a).map _

theorem Ghat_map_irreducible (a : K) [IsLocalRing (B T (a : WithTop K))] :
    Irreducible ((Ghat (T := T) a).map (residue (B T (a : WithTop K)))) := by
  have h1 : ((Ghat (T := T) a).map (residue (B T (a : WithTop K)))).map
      ((resEquiv (T := T) (a : WithTop K)) : ResidueField (B T (a : WithTop K)) →+* E T (a : WithTop K)) =
      F a := by
    apply Polynomial.map_injective (algebraMap (E T (a : WithTop K)) K)
      (algebraMap (E T (a : WithTop K)) K).injective
    have hcomp : (((algebraMap (E T (a : WithTop K)) K).comp
        ((resEquiv (T := T) (a : WithTop K)) : ResidueField (B T (a : WithTop K)) →+* E T (a : WithTop K))).comp
          (residue (B T (a : WithTop K)))).comp
        (mk T (a : WithTop K) : P T (a : WithTop K) →+* B T (a : WithTop K)) =
        (ψ0 T (a : WithTop K) : P T (a : WithTop K) →+* K) :=
      RingHom.ext fun q =>
        (congrArg (algebraMap (E T (a : WithTop K)) K)
          (resEquiv_residue (a : WithTop K) (mk T (a : WithTop K) q))).trans rfl
    rw [Polynomial.map_map, Polynomial.map_map, Ghat, Polynomial.map_map, hcomp, G_map]
  have h2 : Irreducible (Polynomial.mapEquiv (resEquiv (T := T) (a : WithTop K))
      ((Ghat (T := T) a).map (residue (B T (a : WithTop K))))) := by
    rw [Polynomial.mapEquiv_apply, h1]
    exact F_irreducible a
  exact (MulEquiv.irreducible_iff _).mp h2

noncomputable def xa {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : B T x := mk T x (MvPolynomial.X ⟨a, hax.lt⟩)

theorem eval₂_Ghat_xa {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) :
    (Ghat (T := T) a).eval₂ (φ T hax.le : B T (a : WithTop K) →+* B T x) (xa a hax) = 0 := by
  rw [Ghat, Polynomial.eval₂_map, φr_comp_mkr,
    show xa (T := T) a hax = (mk T x : P T x →+* B T x) (MvPolynomial.X ⟨a, hax.lt⟩) from rfl,
    ← Polynomial.hom_eval₂, ← gen_eq x ⟨a, hax.lt⟩ hax.le]
  exact mk_gen x ⟨a, hax.lt⟩

noncomputable def θ₁ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : AdjoinRoot (Ghat (T := T) a) →ₐ[T] B T x :=
  AdjoinRoot.liftAlgHom (Ghat (T := T) a) (φ T hax.le) (xa a hax) (eval₂_Ghat_xa a hax)

theorem θ₁_of {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (r : B T (a : WithTop K)) : θ₁ a hax (AdjoinRoot.of (Ghat (T := T) a) r) = φ T hax.le r :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ r

theorem θ₁_root {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : θ₁ a hax (AdjoinRoot.root (Ghat (T := T) a)) = xa a hax :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

noncomputable def v (x : WithTop K) (a : K) (c : S x) : AdjoinRoot (Ghat (T := T) a) :=
  if h : ((c : K) : WithTop K) < a then
    AdjoinRoot.of (Ghat (T := T) a) (mk T (a : WithTop K) (MvPolynomial.X ⟨c, h⟩))
  else AdjoinRoot.root (Ghat (T := T) a)

theorem v_of_lt (x : WithTop K) (a : K) (c : S x) (h : ((c : K) : WithTop K) < a) :
    v x a c = AdjoinRoot.of (Ghat (T := T) a) (mk T (a : WithTop K) (MvPolynomial.X ⟨c, h⟩)) :=
  dif_pos h

theorem v_a {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : v (T := T) x a ⟨a, hax.lt⟩ = AdjoinRoot.root (Ghat (T := T) a) :=
  dif_neg (lt_irrefl _)

noncomputable def χ (x : WithTop K) (a : K) : P T x →ₐ[T] AdjoinRoot (Ghat (T := T) a) :=
  MvPolynomial.aeval (v x a)

theorem χ_X (x : WithTop K) (a : K) (c : S x) : χ (T := T) x a (MvPolynomial.X c) = v x a c :=
  MvPolynomial.aeval_X _ _

theorem χ_comp_ρ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (z : WithTop K) (hz : z ≤ a) :
    (χ (T := T) x a : P T x →+* AdjoinRoot (Ghat (T := T) a)).comp (ρ T (hz.trans hax.le) : P T z →+* P T x) =
      ((AdjoinRoot.of (Ghat (T := T) a)).comp
        (mk T (a : WithTop K) : P T (a : WithTop K) →+* B T (a : WithTop K))).comp
        (ρ T hz : P T z →+* P T (a : WithTop K)) := by
  refine MvPolynomial.ringHom_ext (fun t => ?_) (fun d => ?_)
  · have h1 : (MvPolynomial.C t : P T z) = algebraMap T (P T z) t := rfl
    change χ x a (ρ T _ (MvPolynomial.C t)) = AdjoinRoot.of _ (mk T _ (ρ T hz (MvPolynomial.C t)))
    simp only [h1, AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply T (B T (a : WithTop K)) (AdjoinRoot (Ghat (T := T) a)) t
  · change χ x a (ρ T _ (MvPolynomial.X d)) = AdjoinRoot.of _ (mk T _ (ρ T hz (MvPolynomial.X d)))
    rw [ρ_X, ρ_X, χ_X, v_of_lt x a _ (lt_of_lt_of_le d.2 hz)]
    rfl

theorem χ_gen {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (c : S x) : χ x a (gen T x c) = 0 := by
  by_cases hc : ((c : K) : WithTop K) < a
  · rw [gen_eq x c (le_of_lt c.2)]
    change (χ (T := T) x a : P T x →+* AdjoinRoot (Ghat (T := T) a)) (Polynomial.eval₂ _ _ _) = 0
    rw [Polynomial.hom_eval₂, χ_comp_ρ a hax _ (le_of_lt hc), AlgHom.coe_toRingHom, χ_X, v_of_lt x a c hc,
      show AdjoinRoot.of (Ghat (T := T) a) (mk T (a : WithTop K) (MvPolynomial.X ⟨c, hc⟩)) =
        ((AdjoinRoot.of (Ghat (T := T) a)).comp
          (mk T (a : WithTop K) : P T (a : WithTop K) →+* B T (a : WithTop K))) (MvPolynomial.X ⟨c, hc⟩)
        from rfl,
      ← Polynomial.hom_eval₂, ← gen_eq (a : WithTop K) ⟨c, hc⟩ (le_of_lt hc)]
    change AdjoinRoot.of _ (mk T _ (gen T (a : WithTop K) ⟨c, hc⟩)) = 0
    rw [mk_gen, map_zero]
  · obtain rfl := eq_of_not_lt a hax c hc
    rw [gen_eq x ⟨a, hax.lt⟩ hax.le]
    change (χ (T := T) x a : P T x →+* AdjoinRoot (Ghat (T := T) a)) (Polynomial.eval₂ _ _ _) = 0
    rw [Polynomial.hom_eval₂, χ_comp_ρ a hax _ le_rfl, ρr_refl, RingHom.comp_id, AlgHom.coe_toRingHom, χ_X,
      v_a a hax, ← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root _

theorem 𝔔_le_ker_χ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : ∀ p ∈ 𝔔 T x, χ x a p = 0 := by
  intro p hp
  have : 𝔔 T x ≤ RingHom.ker (χ (T := T) x a) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨c, rfl⟩
    exact χ_gen a hax c
  exact this hp

noncomputable def θ₂ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : B T x →ₐ[T] AdjoinRoot (Ghat (T := T) a) :=
  Ideal.Quotient.liftₐ (𝔔 T x) (χ x a) (𝔔_le_ker_χ a hax)

theorem θ₂_mk {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (p : P T x) : θ₂ a hax (mk T x p) = χ x a p := rfl

theorem θ₁_comp_θ₂ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : (θ₁ a hax).comp (θ₂ a hax) = AlgHom.id T (B T x) := by
  refine Ideal.Quotient.algHom_ext T ?_
  apply MvPolynomial.algHom_ext
  intro c
  change θ₁ a hax (θ₂ a hax (mk T x (MvPolynomial.X c))) = mk T x (MvPolynomial.X c)
  rw [θ₂_mk, χ_X]
  by_cases hc : ((c : K) : WithTop K) < a
  · rw [v_of_lt x a c hc, θ₁_of, φ_mk, ρ_X]
    rfl
  · obtain rfl := eq_of_not_lt a hax c hc
    rw [v_a a hax, θ₁_root]
    rfl

theorem θ₂_comp_θ₁ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : (θ₂ a hax).comp (θ₁ a hax) = AlgHom.id T (AdjoinRoot (Ghat (T := T) a)) := by
  apply AlgHom.coe_ringHom_injective
  refine Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun r => ?_) ?_)
  · obtain ⟨q, rfl⟩ := mk_surjective (a : WithTop K) r
    change θ₂ a hax (θ₁ a hax (AdjoinRoot.of _ (mk T _ q))) = AdjoinRoot.of _ (mk T _ q)
    rw [θ₁_of, φ_mk, θ₂_mk]
    have := RingHom.congr_fun (χ_comp_ρ a hax (a : WithTop K) le_rfl) q
    rw [ρr_refl, RingHom.comp_id] at this
    exact this
  · change θ₂ a hax (θ₁ a hax (AdjoinRoot.root _)) = AdjoinRoot.root _
    rw [θ₁_root, xa, θ₂_mk, χ_X, v_a a hax]

noncomputable def θ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) : AdjoinRoot (Ghat (T := T) a) ≃ₐ[T] B T x :=
  AlgEquiv.ofAlgHom (θ₁ a hax) (θ₂ a hax) (θ₁_comp_θ₂ a hax) (θ₂_comp_θ₁ a hax)

theorem θ_apply {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (z : AdjoinRoot (Ghat (T := T) a)) : θ a hax z = θ₁ a hax z := rfl

theorem φr_eq_comp {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) :
    (φ T hax.le : B T (a : WithTop K) →+* B T x) =
      (θ₁ (T := T) a hax : AdjoinRoot (Ghat (T := T) a) →+* B T x).comp
        (algebraMap (B T (a : WithTop K)) (AdjoinRoot (Ghat (T := T) a))) :=
  RingHom.ext fun r => (θ₁_of a hax r).symm

theorem good_succ {x : WithTop K} (a : K) (hax : (a : WithTop K) ⋖ x) (IH : Good T (a : WithTop K)) : Good T x := by
  haveI := IH.isLocalRing
  haveI := IH.isNoetherianRing
  haveI : Fact (Irreducible ((Ghat (T := T) a).map (residue (B T (a : WithTop K))))) :=
    ⟨Ghat_map_irreducible a⟩
  obtain ⟨hlocA, hlhA, -, -, hff, hmapA, -⟩ :=
    AdjoinRoot.exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
      (B T (a : WithTop K)) (Ghat (T := T) a) (Ghat_monic a)
  haveI := hlocA
  haveI := hff
  haveI hloc : IsLocalRing (B T x) := (θ a hax).toRingEquiv.isLocalRing
  haveI : IsNoetherianRing (AdjoinRoot (Ghat (T := T) a)) :=
    inferInstanceAs (IsNoetherianRing (Polynomial (B T (a : WithTop K)) ⧸ _))
  have hnoeth : IsNoetherianRing (B T x) := isNoetherianRing_of_ringEquiv _ (θ a hax).toRingEquiv
  have hbij : Function.Bijective (θ₁ (T := T) a hax : AdjoinRoot (Ghat (T := T) a) →+* B T x) :=
    (θ a hax).bijective
  have hflat_a : (φ T hax.le : B T (a : WithTop K) →+* B T x).Flat := by
    rw [φr_eq_comp a hax]
    exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) (RingHom.Flat.of_bijective hbij)
  have hinj_a : Function.Injective (φ T hax.le : B T (a : WithTop K) →+* B T x) := by
    rw [φr_eq_comp a hax, RingHom.coe_comp]
    exact hbij.1.comp (FaithfulSMul.algebraMap_injective _ _)
  have hmap_a : Ideal.map (φ T hax.le : B T (a : WithTop K) →+* B T x)
      (RingHom.ker (ψ T (a : WithTop K) : B T (a : WithTop K) →+* K)) = RingHom.ker (ψ T x : B T x →+* K) := by
    rw [ker_ψ_eq_maximalIdeal, ker_ψ_eq_maximalIdeal, φr_eq_comp a hax, ← Ideal.map_map, hmapA]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ hbij.2
  refine ⟨hloc, hnoeth, ?_, ?_, ?_, ?_, ?_⟩
  · refine RingHom.flat_algebraMap_iff.mp ?_
    rw [← φr_comp_algebraMap hax.le]
    exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr IH.flatT) hflat_a
  · rw [← φr_comp_algebraMap hax.le, ← Ideal.map_map, IH.mapT, hmap_a]
  · intro y h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact (refl_clauses y h).1
    · have hy : y ≤ a := le_of_lt_of_covBy a hax hlt
      rw [← φr_comp hy hax.le]
      exact RingHom.Flat.comp (IH.flat y hy) hflat_a
  · intro y h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact (refl_clauses y h).2.1
    · have hy : y ≤ a := le_of_lt_of_covBy a hax hlt
      have : ⇑(φ T h) = ⇑(φ T hax.le) ∘ ⇑(φ T hy) := funext fun b => (φ_φ hy hax.le b).symm
      rw [this]
      exact hinj_a.comp (IH.inj y hy)
  · intro y h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact (refl_clauses y h).2.2
    · have hy : y ≤ a := le_of_lt_of_covBy a hax hlt
      rw [← φr_comp hy hax.le, ← Ideal.map_map, IH.map y hy, hmap_a]

end Succ

section Lim

variable {x : WithTop K}

theorem 𝔔_eq_iSup (hlim : ∀ y < x, ∃ z, y < z ∧ z < x) :
    𝔔 T x = ⨆ i : {y // y < x}, (𝔔 T i.1).map (ρ T (le_of_lt i.2)) := by
  refine le_antisymm ?_ (iSup_le fun i => 𝔔_map_le _)
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨z, hcz, hzx⟩ := hlim _ c.2
  have h1 : gen T x c = ρ T (le_of_lt hzx) (gen T z ⟨c, hcz⟩) := by rw [ρ_gen]; rfl
  rw [h1]
  exact Submodule.mem_iSup_of_mem (p := fun i : {y // y < x} => (𝔔 T i.1).map (ρ T (le_of_lt i.2)))
    ⟨z, hzx⟩ (Ideal.mem_map_of_mem _ (gen_mem_𝔔 z _))

theorem map𝔔_mono : Monotone (fun i : {y // y < x} => (𝔔 T i.1).map (ρ T (le_of_lt i.2))) := by
  intro i j hij
  change (𝔔 T i.1).map (ρ T (le_of_lt i.2)) ≤ (𝔔 T j.1).map (ρ T (le_of_lt j.2))
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  rw [Ideal.mem_comap, ← ρ_ρ hij (le_of_lt j.2)]
  exact Ideal.mem_map_of_mem _ (𝔔_le_comap hij hq)

theorem inj_lim (hlim : ∀ y < x, ∃ z, y < z ∧ z < x) (IH : ∀ y < x, Good T y) (i : {y // y < x}) :
    Function.Injective (φ T (le_of_lt i.2)) := by
  haveI : Nonempty {y // y < x} := ⟨i⟩
  rw [injective_iff_map_eq_zero]
  intro b hb
  obtain ⟨q, rfl⟩ := mk_surjective i.1 b
  rw [φ_mk, mk_apply, Ideal.Quotient.eq_zero_iff_mem, 𝔔_eq_iSup hlim,
    Submodule.mem_iSup_of_directed _ (map𝔔_mono.directed_le)] at hb
  obtain ⟨j, hj⟩ := hb
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hk : ρ T (le_of_lt i.2) q ∈ (𝔔 T k.1).map (ρ T (le_of_lt k.2)) := map𝔔_mono hjk hj
  rw [← ρ_ρ hik (le_of_lt k.2), ← Ideal.mem_comap, comap_map_ρ] at hk
  have h0 : φ T hik (mk T i.1 q) = 0 := by
    rw [φ_mk, mk_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hk
  exact (injective_iff_map_eq_zero _).mp ((IH k.1 k.2).inj i.1 hik) _ h0

theorem cover_lim (hlim : ∀ y < x, ∃ z, y < z ∧ z < x) (hne : ∃ y, y < x) (b : B T x) :
    ∃ i : {y // y < x}, b ∈ (φ T (le_of_lt i.2) : B T i.1 →+* B T x).range := by
  obtain ⟨y₀, hy₀⟩ := hne
  haveI : Nonempty {y // y < x} := ⟨⟨y₀, hy₀⟩⟩
  obtain ⟨p, rfl⟩ := mk_surjective x b
  obtain ⟨s, q, rfl⟩ := MvPolynomial.exists_finset_rename p
  obtain ⟨M, hM⟩ := Finset.exists_le (s.image fun c : S x => (⟨(c : K), c.2⟩ : {y // y < x}))
  obtain ⟨z, hMz, hzx⟩ := hlim M.1 M.2
  have hs : ∀ c ∈ s, ((c : K) : WithTop K) < z := fun c hc =>
    lt_of_le_of_lt (show ((⟨(c : K), c.2⟩ : {y // y < x}) ≤ M) from hM _ (Finset.mem_image_of_mem _ hc)) hMz
  let f : {c // c ∈ s} → S z := fun c => ⟨(c.1 : K), hs c.1 c.2⟩
  refine ⟨⟨z, hzx⟩, mk T z (MvPolynomial.rename f q), ?_⟩
  change φ T _ (mk T z (MvPolynomial.rename f q)) = mk T x (MvPolynomial.rename Subtype.val q)
  rw [φ_mk, ρ, MvPolynomial.rename_rename]
  rfl

theorem good_lim (hlim : ∀ y < x, ∃ z, y < z ∧ z < x) (hne : ∃ y, y < x) (IH : ∀ y < x, Good T y) :
    Good T x := by
  obtain ⟨y₀, hy₀⟩ := hne
  haveI : Nonempty {y // y < x} := ⟨⟨y₀, hy₀⟩⟩
  let Sr : {y // y < x} → Subring (B T x) := fun i => (φ T (le_of_lt i.2) : B T i.1 →+* B T x).range
  have hmono : Monotone Sr := by
    intro i j hij b hb
    obtain ⟨c, rfl⟩ := hb
    exact ⟨φ T hij c, φ_φ hij (le_of_lt j.2) c⟩
  have hinj : ∀ i : {y // y < x}, Function.Injective (φ T (le_of_lt i.2)) := inj_lim hlim IH
  let e : ∀ i : {y // y < x}, B T i.1 ≃+* Sr i := fun i =>
    RingEquiv.ofBijective (φ T (le_of_lt i.2) : B T i.1 →+* B T x).rangeRestrict
      ⟨fun b₁ b₂ h => hinj i (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  haveI : ∀ i, IsLocalRing (Sr i) := fun i =>
    haveI := (IH i.1 i.2).isLocalRing
    (e i).isLocalRing
  haveI : ∀ i, IsNoetherianRing (Sr i) := fun i =>
    haveI := (IH i.1 i.2).isNoetherianRing
    isNoetherianRing_of_ringEquiv _ (e i)
  have hcomp : ∀ (i j : {y // y < x}) (hij : i ≤ j),
      (Subring.inclusion (hmono hij)).comp (e i : B T i.1 →+* Sr i) =
        (e j : B T j.1 →+* Sr j).comp (φ T hij : B T i.1 →+* B T j.1) := fun i j hij =>
    RingHom.ext fun b => Subtype.ext (φ_φ hij (le_of_lt j.2) b).symm
  have hincl : ∀ (i j : {y // y < x}) (hij : i ≤ j), Subring.inclusion (hmono hij) =
      ((e j : B T j.1 →+* Sr j).comp (φ T hij : B T i.1 →+* B T j.1)).comp
        ((e i).symm : Sr i →+* B T i.1) := by
    intro i j hij
    rw [← hcomp]
    ext b
    simp
  have hmaxSr : ∀ i : {y // y < x}, maximalIdeal (Sr i) =
      Ideal.map (e i : B T i.1 →+* Sr i) (RingHom.ker (ψ T i.1 : B T i.1 →+* K)) := by
    intro i
    haveI := (IH i.1 i.2).isLocalRing
    rw [ker_ψ_eq_maximalIdeal]
    exact (IsLocalRing.map_ringEquiv_maximalIdeal (e i)).symm
  have hmax : ∀ ⦃i j : {y // y < x}⦄ (hij : i ≤ j),
      Ideal.map (Subring.inclusion (hmono hij)) (maximalIdeal (Sr i)) = maximalIdeal (Sr j) := by
    intro i j hij
    rw [hmaxSr i, hmaxSr j, Ideal.map_map, hcomp i j hij, ← Ideal.map_map, (IH j.1 j.2).map i.1 hij]
  have hflat : ∀ ⦃i j : {y // y < x}⦄ (hij : i ≤ j), (Subring.inclusion (hmono hij)).Flat := by
    intro i j hij
    rw [hincl i j hij]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (e i).symm.bijective)
      (RingHom.Flat.comp ((IH j.1 j.2).flat i.1 hij) (RingHom.Flat.of_bijective (e j).bijective))
  obtain ⟨hlocx, hnoethx, hrest⟩ :=
    Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
      (B T x) Sr hmono (cover_lim hlim ⟨y₀, hy₀⟩) hflat hmax
  haveI := hlocx
  have hφ_eq : ∀ i : {y // y < x}, (φ T (le_of_lt i.2) : B T i.1 →+* B T x) =
      (algebraMap (Sr i) (B T x)).comp (e i : B T i.1 →+* Sr i) := fun i => RingHom.ext fun b => rfl
  have hflat_i : ∀ i : {y // y < x}, (φ T (le_of_lt i.2) : B T i.1 →+* B T x).Flat := fun i => by
    haveI := (hrest i).1
    rw [hφ_eq]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (e i).bijective)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hmap_i : ∀ i : {y // y < x}, Ideal.map (φ T (le_of_lt i.2) : B T i.1 →+* B T x)
      (RingHom.ker (ψ T i.1 : B T i.1 →+* K)) = RingHom.ker (ψ T x : B T x →+* K) := fun i => by
    rw [hφ_eq, ← Ideal.map_map, ← hmaxSr i, (hrest i).2, ker_ψ_eq_maximalIdeal]
  refine ⟨hlocx, hnoethx, ?_, ?_, ?_, ?_, ?_⟩
  · refine RingHom.flat_algebraMap_iff.mp ?_
    rw [← φr_comp_algebraMap (le_of_lt hy₀)]
    exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (IH y₀ hy₀).flatT) (hflat_i ⟨y₀, hy₀⟩)
  · rw [← φr_comp_algebraMap (le_of_lt hy₀), ← Ideal.map_map, (IH y₀ hy₀).mapT, hmap_i ⟨y₀, hy₀⟩]
  · intro y h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact (refl_clauses y h).1
    · exact hflat_i ⟨y, hlt⟩
  · intro y h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact (refl_clauses y h).2.1
    · exact hinj ⟨y, hlt⟩
  · intro y h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact (refl_clauses y h).2.2
    · exact hmap_i ⟨y, hlt⟩

end Lim

variable [WellFoundedLT K]

theorem good_all (x : WithTop K) : Good T x := by
  induction x using WellFoundedLT.induction with
  | ind x IH =>
    by_cases hne : ∃ y, y < x
    · by_cases hsucc : ∃ y, y ⋖ x
      · obtain ⟨y, hyx⟩ := hsucc
        obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hyx.lt.ne_top
        exact good_succ a hyx (IH _ hyx.lt)
      · exact good_lim (fun y hy => (not_covBy_iff hy).mp fun h => hsucc ⟨y, h⟩) hne IH
    · exact good_bot x (fun y hy => hne ⟨y, hy⟩)

theorem isLocalHom_ψ_top [IsLocalRing (B T (⊤ : WithTop K))] : IsLocalHom (ψ T (⊤ : WithTop K) : B T (⊤ : WithTop K) →+* K) := by
  refine ⟨fun b hb => ?_⟩
  by_contra hnu
  have hmem : b ∈ maximalIdeal (B T (⊤ : WithTop K)) := (IsLocalRing.mem_maximalIdeal b).2 hnu
  rw [← ker_ψ_eq_maximalIdeal, RingHom.mem_ker] at hmem
  rw [hmem] at hb
  exact not_isUnit_zero hb

theorem ψ_top_surjective : Function.Surjective (ψ T (⊤ : WithTop K) : B T (⊤ : WithTop K) →+* K) := by
  intro z
  have hz : z ∈ E T (⊤ : WithTop K) := IntermediateField.subset_adjoin _ _ (show z ∈ S (⊤ : WithTop K) from WithTop.coe_lt_top z)
  obtain ⟨b, hb⟩ := ψL_surjective (⊤ : WithTop K) ⟨z, hz⟩
  exact ⟨b, congrArg Subtype.val hb⟩

theorem main_ordered :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : Algebra T B)
      (_ : IsLocalHom (algebraMap T B)),
      Module.FaithfullyFlat T B ∧
        Ideal.map (algebraMap T B) (maximalIdeal T) = maximalIdeal B ∧
        Nonempty (ResidueField B ≃ₐ[ResidueField T] K) := by
  have hg := good_all (T := T) (K := K) (⊤ : WithTop K)
  haveI := hg.isLocalRing
  haveI := hg.isNoetherianRing
  haveI := hg.flatT
  have hmap : Ideal.map (algebraMap T (B T (⊤ : WithTop K))) (maximalIdeal T) = maximalIdeal (B T (⊤ : WithTop K)) :=
    hg.mapT.trans (ker_ψ_eq_maximalIdeal (⊤ : WithTop K))
  haveI hlh : IsLocalHom (algebraMap T (B T (⊤ : WithTop K))) := by
    refine ⟨fun t ht => ?_⟩
    by_contra hnu
    have hmem : t ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal t).2 hnu
    have h2 : algebraMap T (B T (⊤ : WithTop K)) t ∈ maximalIdeal (B T (⊤ : WithTop K)) := hmap ▸ Ideal.mem_map_of_mem _ hmem
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 ht
  haveI := isLocalHom_ψ_top (T := T) (K := K)
  let e : ResidueField (B T (⊤ : WithTop K)) ≃+* K :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (ψ T (⊤ : WithTop K) : B T (⊤ : WithTop K) →+* K))
      ⟨(IsLocalRing.ResidueField.lift _).injective, fun z => by
        obtain ⟨b, rfl⟩ := ψ_top_surjective (T := T) (K := K) z
        exact ⟨residue (B T (⊤ : WithTop K)) b, IsLocalRing.ResidueField.lift_residue_apply _ _⟩⟩
  refine ⟨B T (⊤ : WithTop K), inferInstance, inferInstance, inferInstance, inferInstance, hlh,
    Module.FaithfullyFlat.of_flat_of_isLocalHom, hmap, ⟨AlgEquiv.ofRingEquiv (f := e) fun c => ?_⟩⟩
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective c
  have h1 : algebraMap (ResidueField T) (ResidueField (B T (⊤ : WithTop K))) (residue T t) =
      residue (B T (⊤ : WithTop K)) (algebraMap T (B T (⊤ : WithTop K)) t) := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rfl
  rw [h1]
  change IsLocalRing.ResidueField.lift (ψ T (⊤ : WithTop K) : B T (⊤ : WithTop K) →+* K) (residue (B T (⊤ : WithTop K)) (algebraMap T (B T (⊤ : WithTop K)) t)) = _
  rw [IsLocalRing.ResidueField.lift_residue_apply, AlgHom.coe_toRingHom, ψ_algebraMap]
  rfl

end Setup

end P2mResidueExtension
p2m_reactivate "P2MW.S_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic.P2mResidueExtension"

theorem solution
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (K : Type u) [Field K] [Algebra (ResidueField T) K] [Algebra.IsAlgebraic (ResidueField T) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : Algebra T B)
      (_ : IsLocalHom (algebraMap T B)),
      Module.FaithfullyFlat T B ∧
        Ideal.map (algebraMap T B) (maximalIdeal T) = maximalIdeal B ∧
        Nonempty (ResidueField B ≃ₐ[ResidueField T] K) := by
  obtain ⟨_, _⟩ := exists_wellFoundedLT K
  exact P2mResidueExtension.main_ordered

end S_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
end P2MW
export P2MW.S_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic (solution)
