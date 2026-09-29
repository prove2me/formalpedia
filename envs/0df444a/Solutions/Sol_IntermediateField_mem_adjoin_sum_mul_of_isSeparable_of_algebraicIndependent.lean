-- Prove2me | solution 1 for IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3659c3d0-0160-5e5c-817f-4b928153a230

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent

set_option autoImplicit false

open Polynomial

namespace P2mFieldBertini

section Transport

variable {R₁ R₂ L L' : Type*} [Field R₁] [Field R₂] [Field L] [Field L']
  [Algebra R₁ L] [Algebra R₂ L']

theorem isSeparable_transport (e : R₁ ≃+* R₂) (σ : L →+* L')
    (he : ∀ r, algebraMap R₂ L' (e r) = σ (algebraMap R₁ L r)) {y : L}
    (h : IsSeparable R₁ y) : IsSeparable R₂ (σ y) := by
  have hp : (minpoly R₁ y).Separable := h
  have hmap : ((minpoly R₁ y).map e.toRingHom).Separable := hp.map
  have hroot : aeval (σ y) ((minpoly R₁ y).map e.toRingHom) = 0 := by
    rw [aeval_def, eval₂_map]
    have hcomp : (algebraMap R₂ L').comp e.toRingHom = σ.comp (algebraMap R₁ L) := by
      ext r; simp [he]
    rw [hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  exact hmap.of_dvd (minpoly.dvd R₂ (σ y) hroot)

end Transport

section TransportSub

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem isSeparable_of_le {E₁ E₂ : IntermediateField k L} (h : E₁ ≤ E₂) {y : L}
    (hy : IsSeparable E₁ y) : IsSeparable E₂ y := by
  have hp : (minpoly E₁ y).Separable := hy
  set ι : E₁ →+* E₂ := (IntermediateField.inclusion h).toRingHom
  have hmap : ((minpoly E₁ y).map ι).Separable := hp.map
  have hroot : aeval y ((minpoly E₁ y).map ι) = 0 := by
    rw [aeval_def, eval₂_map]
    have hcomp : (algebraMap E₂ L).comp ι = algebraMap E₁ L := by
      ext r; rfl
    rw [hcomp, ← aeval_def, minpoly.aeval]
  exact hmap.of_dvd (minpoly.dvd E₂ y hroot)

theorem transcendental_of_le {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {S₁ S₂ : Subalgebra R A} (h : S₁ ≤ S₂) {t : A} (ht : Transcendental S₂ t) :
    Transcendental S₁ t := by
  rintro ⟨p, hp0, hp⟩
  apply ht
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (Subalgebra.inclusion_injective h)).mpr hp0
  · rw [aeval_def, eval₂_map]
    have hcomp : (algebraMap S₂ A).comp (Subalgebra.inclusion h).toRingHom = algebraMap S₁ A := by
      ext r; rfl
    rw [hcomp, ← aeval_def, hp]

theorem transcendental_of_le' {E₁ E₂ : IntermediateField k L} (h : E₁ ≤ E₂) {t : L}
    (ht : Transcendental E₂ t) : Transcendental E₁ t := by
  rintro ⟨p, hp0, hp⟩
  apply ht
  refine ⟨p.map (IntermediateField.inclusion h).toRingHom, ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (IntermediateField.inclusion_injective h)).mpr hp0
  · rw [aeval_def, eval₂_map]
    have hcomp : (algebraMap E₂ L).comp (IntermediateField.inclusion h).toRingHom =
        algebraMap E₁ L := by
      ext r; rfl
    rw [hcomp, ← aeval_def, hp]

theorem restrictScalars_adjoin_eq (K : Type*) [Field K] [Algebra k K] [Algebra K L]
    [IsScalarTower k K L] (S : Set L) :
    (IntermediateField.adjoin K S).restrictScalars k =
      IntermediateField.adjoin k (Set.range (algebraMap K L) ∪ S) := by
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.restrictScalars_toSubfield, IntermediateField.adjoin_toSubfield,
    IntermediateField.adjoin_toSubfield]
  apply le_antisymm
  · apply Subfield.closure_mono
    exact Set.subset_union_right
  · apply Subfield.closure_le.mpr
    rintro z (⟨a, rfl⟩ | hz)
    · apply Subfield.subset_closure
      exact Or.inl ⟨algebraMap k K a, (IsScalarTower.algebraMap_apply k K L a).symm⟩
    · exact Subfield.subset_closure hz

end TransportSub

theorem separable_scaleRoots {K : Type*} [Field K] {p : K[X]} (hp : p.Separable) {c : K}
    (hc : c ≠ 0) : (p.scaleRoots c).Separable := by
  let E := AlgebraicClosure K
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [← Polynomial.separable_map (algebraMap K E)] at hp ⊢
  have hlc : algebraMap K E p.leadingCoeff ≠ 0 := by
    rw [_root_.map_ne_zero]; exact leadingCoeff_ne_zero.mpr hp0
  rw [map_scaleRoots _ _ _ hlc]
  have hp0' : p.map (algebraMap K E) ≠ 0 := Polynomial.map_ne_zero hp0
  have hc' : IsUnit (algebraMap K E c) := (IsUnit.mk0 c hc).map _
  rw [← nodup_roots_iff_of_splits (scaleRoots_ne_zero hp0' _) (IsAlgClosed.splits _),
    roots_scaleRoots _ hc']
  exact (nodup_roots hp).map (mul_right_injective₀ hc'.ne_zero)

section SC1

variable {F M L : Type*} [Field F] [Field M] [Field L] [Algebra F L] [Algebra M L]

open IntermediateField in

theorem mem_adjoin_simple_of_isSeparable_of_transcendental [Infinite F]
    (φ : F →+* M) (hφ : ∀ a, algebraMap M L (φ a) = algebraMap F L a)
    (hsc : ∀ m : M, IsSeparable F (algebraMap M L m) → ∃ a, φ a = m)
    {t : L} (ht : Transcendental M t) {y : L} (hy : y ∈ M⟮t⟯)
    (hsep : IsSeparable F⟮t⟯ y) : y ∈ F⟮t⟯ := by
  classical

  set Ft : IntermediateField F L := F⟮t⟯ with hFt
  let ιF : F[X] →ₐ[F] L := aeval t
  let ιM : M[X] →ₐ[M] L := aeval t
  have hcompRing : (algebraMap M L).comp φ = algebraMap F L := RingHom.ext hφ
  have hcomp : ∀ p : F[X], ιM (p.map φ) = ιF p := by
    intro p
    change aeval t (p.map φ) = aeval t p
    rw [aeval_def, eval₂_map, hcompRing, ← aeval_def]
  have hιM_inj : Function.Injective ιM := transcendental_iff_injective.mp ht
  have htF : Transcendental F t := by
    rw [transcendental_iff_injective]
    intro p q hpq
    have : ιM (p.map φ) = ιM (q.map φ) := by rw [hcomp, hcomp]; exact hpq
    exact Polynomial.map_injective φ φ.injective (hιM_inj this)
  have hιF_inj : Function.Injective ιF := transcendental_iff_injective.mp htF
  have hιF_mem : ∀ p : F[X], ιF p ∈ Ft := fun p =>
    algebra_adjoin_le_adjoin F {t} (aeval_mem_adjoin_singleton F t)

  set q : Ft[X] := minpoly Ft y with hq
  have hyint : IsIntegral Ft y := hsep.isIntegral
  have hqmonic : q.Monic := minpoly.monic hyint
  have hqsep : q.Separable := hsep
  have hqy : aeval y q = 0 := minpoly.aeval Ft y
  set d : ℕ := q.natDegree with hd

  have hrep : ∀ i : ℕ, ∃ r s : F[X], ιF s ≠ 0 ∧ (q.coeff i : L) * ιF s = ιF r := by
    intro i
    have hmem : (q.coeff i : L) ∈ F⟮t⟯ := (q.coeff i).2
    obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff F _).mp hmem
    by_cases hs : aeval t s = 0
    · refine ⟨0, 1, ?_, ?_⟩
      · change aeval t (1 : F[X]) ≠ 0; simp
      · rw [hrs, hs, div_zero, zero_mul]; change (0 : L) = aeval t (0 : F[X]); simp
    · refine ⟨r, s, hs, ?_⟩
      rw [hrs]; change aeval t r / aeval t s * aeval t s = aeval t r
      exact div_mul_cancel₀ _ hs
  choose r s hs hrs using hrep

  set c : F[X] := ∏ i ∈ Finset.range d, s i with hc
  have hcL : ιF c = ∏ i ∈ Finset.range d, ιF (s i) := by simp [hc, map_prod]
  have hcL0 : ιF c ≠ 0 := by
    rw [hcL]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hs i
  set qL : L[X] := q.map (algebraMap Ft L) with hqL
  have hqLmonic : qL.Monic := hqmonic.map _
  have hqLdeg : qL.natDegree = d := by rw [hqL, hqmonic.natDegree_map]
  have hqLsep : qL.Separable := hqsep.map
  set QL : L[X] := qL.scaleRoots (ιF c) with hQL
  set y₁ : L := ιF c * y with hy₁
  have hQLy₁ : aeval y₁ QL = 0 := by
    have h1 : aeval y qL = 0 := by rw [hqL, aeval_map_algebraMap]; exact hqy
    have := scaleRoots_aeval_eq_zero (r := ιF c) h1
    simpa using this
  have hQLsep : QL.Separable := separable_scaleRoots hqLsep hcL0
  have hQLmonic : QL.Monic := (monic_scaleRoots_iff _).mpr hqLmonic
  have hQLdeg : QL.natDegree = d := by rw [hQL, natDegree_scaleRoots, hqLdeg]

  have hQLlifts : QL ∈ Polynomial.lifts (ιF : F[X] →+* L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [hQL, coeff_scaleRoots, hqLdeg]
    rcases lt_trichotomy i d with hi | rfl | hi
    ·
      have hdi : d - i = (d - 1 - i) + 1 := by omega
      have hi' : i ∈ Finset.range d := Finset.mem_range.mpr hi
      have key : (algebraMap Ft L (q.coeff i)) * ιF c =
          ιF (r i) * ∏ j ∈ (Finset.range d).erase i, ιF (s j) := by
        rw [hcL, ← Finset.mul_prod_erase _ _ hi', ← mul_assoc]
        exact congrArg (· * _) (hrs i)
      refine ⟨r i * (∏ j ∈ (Finset.range d).erase i, s j) * c ^ (d - 1 - i), ?_⟩
      change ιF _ = _
      rw [hqL, coeff_map, map_mul, map_mul, map_pow, map_prod, hdi, pow_succ', ← mul_assoc, key]
    · exact ⟨1, by
        change ιF 1 = _
        rw [map_one, Nat.sub_self, pow_zero, mul_one]
        change (1 : L) = ((q.map (algebraMap Ft L)).coeff q.natDegree)
        rw [coeff_map, hqmonic.coeff_natDegree, map_one]⟩
    · refine ⟨0, ?_⟩
      change ιF 0 = _
      rw [map_zero, coeff_eq_zero_of_natDegree_lt (hqLdeg ▸ hi), zero_mul]
  obtain ⟨Q, hQmap, -, hQmonic⟩ := lifts_and_degree_eq_and_monic hQLlifts hQLmonic
  have hQdeg : Q.natDegree = d := by
    rw [← hQLdeg, ← hQmap, hQmonic.natDegree_map]

  let KM := FractionRing M[X]
  let lamM : KM →ₐ[M] L := IsFractionRing.liftAlgHom (K := KM) hιM_inj
  have hlamM_alg : ∀ p : M[X], lamM (algebraMap M[X] KM p) = ιM p := fun p => by
    simp [lamM]
  have hlamM_range : lamM.fieldRange = M⟮t⟯ :=
    IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq hιM_inj
      (Algebra.adjoin_singleton_eq_range_aeval M t).symm
  obtain ⟨Y, hY⟩ : ∃ Y : KM, lamM Y = y := by
    have : y ∈ lamM.fieldRange := hlamM_range ▸ hy
    exact AlgHom.mem_fieldRange.mp this
  set QM : M[X][X] := Q.map (mapRingHom φ) with hQM
  have hQMmonic : QM.Monic := hQmonic.map _
  have hcompHom : (ιM : M[X] →+* L).comp (mapRingHom φ) = (ιF : F[X] →+* L) := by
    ext p
    · simp [ιM, ιF, hφ]
    · simp [ιM, ιF]
  have hevalQM : eval₂ (ιM : M[X] →+* L) y₁ QM = 0 := by
    rw [hQM, eval₂_map, hcompHom]
    have : eval₂ (ιF : F[X] →+* L) y₁ Q = aeval y₁ (Q.map (ιF : F[X] →+* L)) := by
      rw [aeval_def, eval₂_map]; rfl
    rw [this, hQmap, hQLy₁]
  set Y₁ : KM := algebraMap M[X] KM (c.map φ) * Y with hY₁
  have hlamY₁ : lamM Y₁ = y₁ := by
    rw [hY₁, map_mul, hlamM_alg, hY, hcomp]
  have hY₁root : aeval Y₁ QM = 0 := by
    apply (lamM : KM →+* L).injective
    rw [map_zero, aeval_def, hom_eval₂]
    have : (lamM : KM →+* L).comp (algebraMap M[X] KM) = (ιM : M[X] →+* L) := by
      ext p
      · simp [hlamM_alg]
      · simp [hlamM_alg, ιM]
    rw [this]
    change eval₂ _ (lamM Y₁) QM = 0
    rw [hlamY₁, hevalQM]
  obtain ⟨w, hw⟩ : ∃ w : M[X], algebraMap M[X] KM w = Y₁ :=
    isInteger_of_is_root_of_monic hQMmonic hY₁root
  have hy₁w : y₁ = ιM w := by rw [← hlamY₁, ← hw, hlamM_alg]

  have hQMw : QM.eval w = 0 := by
    apply hιM_inj
    rw [map_zero]
    change (ιM : M[X] →+* L) (QM.eval w) = 0
    rw [← eval₂_at_apply]
    change eval₂ (ιM : M[X] →+* L) (ιM w) QM = 0
    rw [← hy₁w, hevalQM]

  have hspec : ∀ a : F, eval₂ φ (w.eval (φ a)) (Q.map (evalRingHom a)) = 0 := by
    intro a
    have h1 : eval₂ (evalRingHom (φ a)) (w.eval (φ a)) QM = 0 := by
      rw [show w.eval (φ a) = evalRingHom (φ a) w from rfl, eval₂_at_apply, hQMw, map_zero]
    rw [hQM, eval₂_map] at h1
    have hcomm : (evalRingHom (φ a)).comp (mapRingHom φ) = φ.comp (evalRingHom a) := by
      ext p
      · simp
      · simp
    rw [hcomm, ← eval₂_map] at h1
    exact h1

  set Res : F[X] := Q.resultant (derivative Q) with hRes
  have hRes0 : Res ≠ 0 := by
    intro h0
    have h1 : (ιF : F[X] →+* L) Res = 0 := by rw [h0, map_zero]
    rw [hRes, ← resultant_map_map, ← derivative_map, hQmap] at h1

    have hle : (derivative QL).natDegree ≤ (derivative Q).natDegree := by
      rw [← hQmap, derivative_map]; exact natDegree_map_le
    obtain ⟨kk, hkk⟩ := Nat.exists_eq_add_of_le hle
    rw [hkk, resultant_add_right_deg _ _ _ _ _ le_rfl, hQdeg, ← hQLdeg,
      hQLmonic.coeff_natDegree, one_pow, one_mul] at h1
    exact resultant_ne_zero _ _ hQLsep h1
  have hgood : ∀ a : F, Res.eval a ≠ 0 → (Q.map (evalRingHom a)).Separable := by
    intro a ha
    set Qa := Q.map (evalRingHom a) with hQa
    have hQamonic : Qa.Monic := hQmonic.map _
    have hQadeg : Qa.natDegree = d := by rw [hQa, hQmonic.natDegree_map, hQdeg]
    have h1 : (evalRingHom a) Res ≠ 0 := ha
    rw [hRes, ← resultant_map_map, ← derivative_map] at h1
    have hle : (derivative Qa).natDegree ≤ (derivative Q).natDegree := by
      rw [hQa, derivative_map]; exact natDegree_map_le
    obtain ⟨kk, hkk⟩ := Nat.exists_eq_add_of_le hle
    rw [← hQa, hkk, resultant_add_right_deg _ _ _ _ _ le_rfl, hQdeg, ← hQadeg,
      hQamonic.coeff_natDegree, one_pow, one_mul] at h1
    exact (isUnit_resultant_iff_isCoprime hQamonic).mp (Ne.isUnit h1)

  have hval : ∀ a : F, Res.eval a ≠ 0 → ∃ b : F, φ b = w.eval (φ a) := by
    intro a ha
    apply hsc
    set z : L := algebraMap M L (w.eval (φ a))
    have hz : aeval z (Q.map (evalRingHom a)) = 0 := by
      rw [aeval_def, ← hcompRing]
      change eval₂ ((algebraMap M L).comp φ) (algebraMap M L (w.eval (φ a))) _ = 0
      rw [← hom_eval₂, hspec a, map_zero]
    exact (hgood a ha).of_dvd (minpoly.dvd F z hz)

  obtain ⟨S, hSsub, hScard⟩ : ∃ S : Finset F, (↑S : Set F) ⊆ {a | Res.eval a ≠ 0} ∧
      S.card = w.natDegree + 1 := by
    have hfin : {a : F | Res.eval a = 0}.Finite := by
      have : {a : F | Res.eval a = 0} ⊆ ↑Res.roots.toFinset := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha
        simp [mem_roots hRes0, ha]
      exact (Finset.finite_toSet _).subset this
    have hinf : {a : F | Res.eval a ≠ 0}.Infinite := by
      have := hfin.infinite_compl
      convert this using 1
      ext a; simp
    exact hinf.exists_subset_card_eq _
  have hSgood : ∀ a ∈ S, ∃ b : F, φ b = w.eval (φ a) := fun a ha => hval a (hSsub ha)
  choose! b hb using hSgood
  set w₀ : F[X] := Lagrange.interpolate S id b with hw₀
  have hw₀deg : w₀.degree < S.card := Lagrange.degree_interpolate_lt _ (Set.injOn_id _)
  have hw₀eval : ∀ a ∈ S, w₀.eval a = b a := fun a ha =>
    Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) ha
  have hww₀ : w = w₀.map φ := by
    apply eq_of_degrees_lt_of_eval_finset_eq (S.image φ)
    · rw [Finset.card_image_of_injective _ φ.injective, hScard]
      exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    · rw [Finset.card_image_of_injective _ φ.injective, degree_map]
      exact hw₀deg
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      rw [eval_map, eval₂_at_apply, hw₀eval a ha, hb a ha]

  have hy₁mem : y₁ ∈ Ft := by
    rw [hy₁w, hww₀, hcomp]; exact hιF_mem w₀
  have : y = (ιF c)⁻¹ * y₁ := by
    rw [hy₁, ← mul_assoc, inv_mul_cancel₀ hcL0, one_mul]
  rw [this]
  exact mul_mem (inv_mem (hιF_mem c)) hy₁mem

end SC1

open IntermediateField

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

def SepClosedIn (F M : IntermediateField k L) : Prop :=
  ∀ y : L, y ∈ M → IsSeparable F y → y ∈ F

theorem SepClosedIn.mono_right {F M M' : IntermediateField k L} (h : SepClosedIn F M)
    (hM : M' ≤ M) : SepClosedIn F M' := fun y hy hs => h y (hM hy) hs

theorem adjoin_coe_adjoin_union (S T : Set L) :
    adjoin k ((adjoin k S : Set L) ∪ T) = adjoin k (S ∪ T) := by
  rw [← restrictScalars_adjoin, adjoin_adjoin_left]

theorem SepClosedIn.adjoin_transcendental [Infinite k] {F M : IntermediateField k L}
    (hFM : F ≤ M) (h : SepClosedIn F M) {t : L} (ht : Transcendental M t) :
    SepClosedIn ((adjoin F {t}).restrictScalars k) ((adjoin M {t}).restrictScalars k) := by
  intro y hy hsep
  haveI : Infinite F := Infinite.of_injective (algebraMap k F) (algebraMap k F).injective
  let φ : F →+* M := (IntermediateField.inclusion hFM).toRingHom
  have hφ : ∀ a, algebraMap M L (φ a) = algebraMap F L a := fun a => rfl
  have hsc : ∀ m : M, IsSeparable F (algebraMap M L m) → ∃ a, φ a = m := by
    intro m hm
    have hmF : (m : L) ∈ F := h m m.2 hm
    exact ⟨⟨m, hmF⟩, Subtype.ext rfl⟩
  have hy' : y ∈ adjoin M {t} := hy
  have hsep' : IsSeparable (adjoin F {t}) y := hsep
  exact mem_adjoin_simple_of_isSeparable_of_transcendental φ hφ hsc ht hy' hsep'

theorem SepClosedIn.adjoin_transcendental' [Infinite k] {S T : Set L}
    (hST : S ⊆ T) (h : SepClosedIn (adjoin k S) (adjoin k T)) {t : L}
    (ht : Transcendental (adjoin k T) t) :
    SepClosedIn (adjoin k (S ∪ {t})) (adjoin k (T ∪ {t})) := by
  have := h.adjoin_transcendental (adjoin.mono k _ _ hST) ht
  rwa [adjoin_adjoin_left, adjoin_adjoin_left] at this

theorem isSeparable_of_isSeparable_bot {y : L} (h : IsSeparable (⊥ : IntermediateField k L) y) :
    IsSeparable k y := by
  have := isSeparable_transport (L := L) (L' := L) (botEquiv k L).toRingEquiv (RingHom.id L)
    (fun r => ?_) h
  · simpa using this
  · obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp r.2
    have hr : r = algebraMap k (⊥ : IntermediateField k L) a := Subtype.ext ha.symm
    rw [hr]
    change algebraMap k L (botEquiv k L (algebraMap k _ a)) = (algebraMap k (⊥ : IntermediateField k L) a : L)
    rw [botEquiv_def]
    rfl

section Permanence

variable [Infinite k] (K : Type*) [Field K] [Algebra k K] [Algebra K L] [IsScalarTower k K L]

theorem sepClosedIn_adjoin_image
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {ι : Type*} (x : ι → L) (hx : AlgebraicIndependent K x) (s : Finset ι) :
    SepClosedIn (adjoin k (x '' ↑s)) (adjoin k (Set.range (algebraMap K L) ∪ x '' ↑s)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy hsep
    have hE : adjoin k (x '' ((∅ : Finset ι) : Set ι)) = (⊥ : IntermediateField k L) := by simp

    have hle : adjoin k (Set.range (algebraMap K L) ∪ x '' ((∅ : Finset ι) : Set ι)) ≤
        (IsScalarTower.toAlgHom k K L).fieldRange := by
      apply adjoin_le_iff.mpr
      rintro _ (⟨θ, rfl⟩ | ⟨_, h, _⟩)
      · exact ⟨θ, rfl⟩
      · simp at h
    obtain ⟨θ, rfl⟩ := AlgHom.mem_fieldRange.mp (hle hy)
    rw [hE] at hsep ⊢
    have h1 : IsSeparable k (algebraMap K L θ) := isSeparable_of_isSeparable_bot hsep
    have h2 : IsSeparable k θ := IsSeparable.tower_bot h1
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp (hsc θ h2)
    change algebraMap K L θ ∈ (⊥ : IntermediateField k L)
    rw [← ha, ← IsScalarTower.algebraMap_apply]
    exact IntermediateField.algebraMap_mem _ a
  | insert i s hi IH =>
    have ht : Transcendental (adjoin k (Set.range (algebraMap K L) ∪ x '' ↑s)) (x i) := by
      have h1 : Transcendental (Algebra.adjoin K (x '' ↑s)) (x i) :=
        hx.transcendental_adjoin (s := ↑s) (by exact_mod_cast hi)
      have h2 : Transcendental (IntermediateField.adjoin K (x '' ↑s)) (x i) :=
        IntermediateField.transcendental_adjoin_iff.mpr h1
      have h3 : Transcendental ((IntermediateField.adjoin K (x '' ↑s)).restrictScalars k) (x i) := h2
      rwa [restrictScalars_adjoin_eq] at h3
    have := IH.adjoin_transcendental' (Set.subset_union_right) ht
    rw [Finset.coe_insert, Set.image_insert_eq, ← Set.union_singleton, ← Set.union_assoc]
    exact this

theorem sepClosedIn_adjoin_range
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {ι : Type*} [Fintype ι] (x : ι → L) (hx : AlgebraicIndependent K x) :
    SepClosedIn (adjoin k (Set.range x)) (adjoin k (Set.range (algebraMap K L) ∪ Set.range x)) := by
  have := sepClosedIn_adjoin_image K hsc x hx Finset.univ
  simpa [Set.image_univ] using this

end Permanence

section FinSep

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem linearIndependent_powerBasis_over_adjoin {ι : Type*} {x : ι → E}
    (hx : AlgebraicIndependent F x) {α : E} (hα : IsIntegral F α) :
    LinearIndependent (adjoin F (Set.range x))
      (fun i => ((adjoin.powerBasis hα).basis i : E)) := by
  classical
  set A : IntermediateField F E := F⟮α⟯
  set pb := adjoin.powerBasis hα
  haveI : FiniteDimensional F A := adjoin.finiteDimensional hα
  haveI : Algebra.IsAlgebraic F A := Algebra.IsAlgebraic.of_finite F A
  have hxA : AlgebraicIndependent A x := hx.extendScalars A

  rw [← LinearIndependent.iff_fractionRing (Algebra.adjoin F (Set.range x))
    (adjoin F (Set.range x))]
  rw [linearIndependent_iff']
  intro u g hsum i hi

  let P : _ → MvPolynomial ι F := fun j => hx.aevalEquiv.symm (g j)
  have hgP : ∀ j, (g j : E) = MvPolynomial.aeval x (P j) := by
    intro j
    have : g j = hx.aevalEquiv (P j) := by simp [P]
    conv_lhs => rw [this]
    rfl

  set Q : MvPolynomial ι A :=
    ∑ j ∈ u, MvPolynomial.C (pb.basis j) * MvPolynomial.map (algebraMap F A) (P j) with hQ
  have hQ0 : MvPolynomial.aeval x Q = 0 := by
    rw [hQ, map_sum]
    have : ∀ j ∈ u, MvPolynomial.aeval x (MvPolynomial.C (pb.basis j) *
        MvPolynomial.map (algebraMap F A) (P j)) = (g j : E) * (pb.basis j : E) := by
      intro j _
      rw [map_mul, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_C, hgP, mul_comm]
      rfl
    rw [Finset.sum_congr rfl this]
    simpa [Algebra.smul_def] using hsum
  have hQzero : Q = 0 := hxA.eq_zero_of_aeval_eq_zero Q hQ0

  have hcoeff : ∀ m : ι →₀ ℕ, ∑ j ∈ u, (P j).coeff m • pb.basis j = 0 := by
    intro m
    have := congrArg (MvPolynomial.coeff m) hQzero
    rw [hQ, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, Algebra.smul_def, mul_comm]
  have hPzero : ∀ j ∈ u, P j = 0 := by
    intro j hj
    ext m
    have := linearIndependent_iff'.mp pb.basis.linearIndependent u (fun j => (P j).coeff m)
      (hcoeff m) j hj
    simpa using this
  have : g i = hx.aevalEquiv (P i) := by simp [P]
  rw [this, hPzero i hi, map_zero]

theorem exists_bound_finrank_adjoin_of_fg (hfg : (⊤ : IntermediateField F E).FG) :
    ∃ N : ℕ, ∀ α : E, IsIntegral F α → Module.finrank F F⟮α⟯ ≤ N := by
  classical
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis F E
  set FT : IntermediateField F E := adjoin F (Set.range (Subtype.val : T → E)) with hFT
  haveI halg : Algebra.IsAlgebraic FT E := hT.isAlgebraic_field

  obtain ⟨G, hG⟩ := hfg
  haveI hfin : FiniteDimensional FT E := by
    have h1 : adjoin FT (G : Set E) = ⊤ := by
      apply restrictScalars_injective F
      rw [restrictScalars_top, eq_top_iff, ← hG, restrictScalars_adjoin]
      exact adjoin.mono F _ _ Set.subset_union_right
    haveI : FiniteDimensional FT (adjoin FT (G : Set E)) :=
      finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic (R := FT) z).isIntegral
    rw [h1] at this
    exact topEquiv.toLinearEquiv.finiteDimensional
  refine ⟨Module.finrank FT E, fun α hα => ?_⟩
  have hli := linearIndependent_powerBasis_over_adjoin hT.1 hα
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  rw [(adjoin.powerBasis hα).finrank]
  exact this

theorem exists_isSeparable_forall_mem_adjoin_of_fg (hfg : (⊤ : IntermediateField F E).FG) :
    ∃ γ : E, IsSeparable F γ ∧ ∀ θ : E, IsSeparable F θ → θ ∈ F⟮γ⟯ := by
  classical
  obtain ⟨N, hN⟩ := exists_bound_finrank_adjoin_of_fg hfg
  let P : ℕ → Prop := fun n => ∃ γ : E, IsSeparable F γ ∧ n ≤ Module.finrank F F⟮γ⟯
  set m := Nat.findGreatest P N with hm
  have hP0 : P 0 := ⟨0, by
    have : (0 : E) = algebraMap F E 0 := (map_zero _).symm
    rw [this]; exact isSeparable_algebraMap (0 : F), Nat.zero_le _⟩
  have hPm : P m := Nat.findGreatest_spec (Nat.zero_le N) hP0
  obtain ⟨γ, hγsep, hγdeg⟩ := hPm
  refine ⟨γ, hγsep, fun θ hθ => ?_⟩

  haveI : Algebra.IsSeparable F F⟮γ, θ⟯ := isSeparable_adjoin_pair_of_isSeparable F E hγsep hθ
  haveI : FiniteDimensional F F⟮γ, θ⟯ := by
    apply finiteDimensional_adjoin
    rintro z (rfl | rfl)
    exacts [hγsep.isIntegral, hθ.isIntegral]
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element F F⟮γ, θ⟯
  have hβE : F⟮(β : E)⟯ = F⟮γ, θ⟯ := by
    rw [← lift_adjoin_simple, hβ, lift_top]
  have hβsep : IsSeparable F (β : E) := by
    have := Algebra.IsSeparable.isSeparable F β
    exact (isSeparable_map_iff (F⟮γ, θ⟯).val Subtype.val_injective).mpr this

  have hβdeg : Module.finrank F F⟮(β : E)⟯ ≤ m := by
    have hle : Module.finrank F F⟮(β : E)⟯ ≤ N := hN _ hβsep.isIntegral
    exact Nat.le_findGreatest hle ⟨β, hβsep, le_rfl⟩
  have hγle : F⟮γ⟯ ≤ F⟮(β : E)⟯ := by
    rw [hβE]; apply adjoin.mono; simp
  haveI : FiniteDimensional F F⟮(β : E)⟯ := adjoin.finiteDimensional hβsep.isIntegral
  have heq : F⟮γ⟯ = F⟮(β : E)⟯ :=
    eq_of_le_of_finrank_le hγle (hβdeg.trans hγdeg)
  rw [heq, hβE]
  exact subset_adjoin F _ (by simp)

theorem exists_ne_adjoin_simple_eq {α : Type*} [Infinite α]
    (hfg : (⊤ : IntermediateField F E).FG) (θ : α → E) (hθ : ∀ a, IsSeparable F (θ a)) :
    ∃ a₁ a₂, a₁ ≠ a₂ ∧ F⟮θ a₁⟯ = F⟮θ a₂⟯ := by
  classical
  obtain ⟨γ, hγsep, hγall⟩ := exists_isSeparable_forall_mem_adjoin_of_fg hfg
  set S₀ : IntermediateField F E := F⟮γ⟯ with hS₀
  have hθmem : ∀ a, θ a ∈ S₀ := fun a => hγall _ (hθ a)
  haveI : FiniteDimensional F S₀ := adjoin.finiteDimensional hγsep.isIntegral
  haveI : Algebra.IsAlgebraic F S₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI : Finite (IntermediateField F S₀) := by
    apply Field.finite_intermediateField_of_exists_primitive_element
    refine ⟨⟨γ, mem_adjoin_simple_self F γ⟩, ?_⟩
    apply lift_injective
    rw [lift_adjoin_simple, lift_top]
  let Φ : α → IntermediateField F S₀ := fun a => F⟮(⟨θ a, hθmem a⟩ : S₀)⟯
  obtain ⟨a₁, a₂, hne, hΦ⟩ := Finite.exists_ne_map_eq_of_infinite Φ
  refine ⟨a₁, a₂, hne, ?_⟩
  have := congrArg lift hΦ
  simpa only [Φ, lift_adjoin_simple] using this

end FinSep

section Bookkeeping

variable {K : Type*} [Field K] [Algebra k K] [Algebra K L] [IsScalarTower k K L]

theorem map_adjoin_range_union_singleton {ι : Type*} (σ : L ≃ₐ[k] L) (x : ι → L) (b : ι → k)
    (hσx : ∀ i, σ (x i) = x i + algebraMap k L (b i)) (ξ ξ' : L) (hσξ : σ ξ = ξ') :
    (adjoin k (Set.range x ∪ {ξ})).map (σ : L →ₐ[k] L) = adjoin k (Set.range x ∪ {ξ'}) := by
  rw [adjoin_map]
  apply le_antisymm
  · apply adjoin_le_iff.mpr
    rintro _ ⟨z, hz | hz, rfl⟩
    · obtain ⟨i, rfl⟩ := hz
      change σ (x i) ∈ adjoin k (Set.range x ∪ {ξ'})
      rw [hσx]
      exact add_mem (subset_adjoin k _ (Or.inl ⟨i, rfl⟩)) (IntermediateField.algebraMap_mem _ _)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      change σ z ∈ adjoin k (Set.range x ∪ {ξ'})
      rw [hσξ]
      exact subset_adjoin k _ (Or.inr rfl)
  · apply adjoin_le_iff.mpr
    rintro z (⟨i, rfl⟩ | hz)
    · have : x i = σ (x i) - algebraMap k L (b i) := by rw [hσx]; ring
      rw [this]
      exact sub_mem (subset_adjoin k _ ⟨x i, Or.inl ⟨i, rfl⟩, rfl⟩)
        (IntermediateField.algebraMap_mem _ _)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [← hσξ]
      exact subset_adjoin k _ ⟨ξ, Or.inr rfl, rfl⟩

theorem fg_top_of_adjoin_eq_top (hfg : (⊤ : IntermediateField k K).FG) {S : Set L}
    (htop : adjoin k (Set.range (algebraMap K L) ∪ S) = ⊤) (E : IntermediateField k L)
    (hS : S ⊆ E) : (⊤ : IntermediateField E L).FG := by
  classical
  obtain ⟨G, hG⟩ := hfg
  refine ⟨G.image (algebraMap K L), ?_⟩
  apply restrictScalars_injective k
  rw [restrictScalars_top, restrictScalars_adjoin, eq_top_iff, ← htop]
  apply adjoin_le_iff.mpr
  rintro z (⟨y, rfl⟩ | hz)
  · have hy : y ∈ adjoin k (G : Set K) := by rw [hG]; exact mem_top
    have : algebraMap K L y ∈ (adjoin k (G : Set K)).map (IsScalarTower.toAlgHom k K L) :=
      ⟨y, hy, rfl⟩
    rw [adjoin_map] at this
    refine adjoin.mono k _ _ ?_ this
    intro w hw
    refine Or.inr ?_
    rw [Finset.coe_image]
    exact hw
  · exact subset_adjoin k _ (Or.inl (hS hz))

theorem mem_of_two_shifts (N : IntermediateField k L) {ξ δ : L} {a₁ a₂ : k} (hne : a₁ ≠ a₂)
    (h₁ : ξ + algebraMap k L a₁ * δ ∈ N) (h₂ : ξ + algebraMap k L a₂ * δ ∈ N) :
    ξ ∈ N ∧ δ ∈ N := by
  have hα : algebraMap k L a₂ - algebraMap k L a₁ ≠ 0 := by
    rw [← map_sub]; exact (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hδeq : δ = (algebraMap k L a₂ - algebraMap k L a₁)⁻¹ *
      ((ξ + algebraMap k L a₂ * δ) - (ξ + algebraMap k L a₁ * δ)) := by
    rw [eq_inv_mul_iff_mul_eq₀ hα]; ring
  have hδN : δ ∈ N := by
    rw [hδeq]
    exact mul_mem (inv_mem (sub_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.algebraMap_mem _ _))) (sub_mem h₂ h₁)
  refine ⟨?_, hδN⟩
  have hξeq : ξ = (ξ + algebraMap k L a₁ * δ) - algebraMap k L a₁ * δ := by ring
  rw [hξeq]
  exact sub_mem h₁ (mul_mem (IntermediateField.algebraMap_mem _ _) hδN)

end Bookkeeping

section Omega

variable (k K : Type*) [Field k] [Field K] [Algebra k K] (n : ℕ)

noncomputable def tau (b : Fin (n + 1) → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (b i))
    (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (b i))
    (by ext i : 1; simp)
    (by ext i : 1; simp)

@[scoped simp] theorem tau_X (b : Fin (n + 1) → K) (i : Fin (n + 1)) :
    tau K n b (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (b i) := by
  simp [tau]

noncomputable def sigma (b : Fin (n + 1) → K) :
    FractionRing (MvPolynomial (Fin (n + 1)) K) ≃ₐ[k] FractionRing (MvPolynomial (Fin (n + 1)) K) :=
  (IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (MvPolynomial (Fin (n + 1)) K))
    (L := FractionRing (MvPolynomial (Fin (n + 1)) K)) (tau K n b)).restrictScalars k

theorem sigma_algebraMap (b : Fin (n + 1) → K) (p : MvPolynomial (Fin (n + 1)) K) :
    sigma k K n b (algebraMap _ _ p) = algebraMap _ _ (tau K n b p) := by
  simp [sigma]

theorem sigma_X (b : Fin (n + 1) → K) (i : Fin (n + 1)) :
    sigma k K n b (algebraMap _ _ (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)) =
      algebraMap _ _ (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) + algebraMap K _ (b i) := by
  rw [sigma_algebraMap, tau_X, map_add]
  congr 1

theorem sigma_algebraMap_K (b : Fin (n + 1) → K) (g : K) :
    sigma k K n b (algebraMap K _ g) = algebraMap K _ g := by
  change (IsFractionRing.algEquivOfAlgEquiv _ : _ ≃ₐ[K] _) _ = _
  exact AlgEquiv.commutes _ g

theorem adjoin_range_union_range_X_eq_top :
    adjoin k (Set.range (algebraMap K (FractionRing (MvPolynomial (Fin (n + 1)) K))) ∪
      Set.range (fun i => algebraMap (MvPolynomial (Fin (n + 1)) K)
        (FractionRing (MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X i))) = ⊤ := by
  set Ω := FractionRing (MvPolynomial (Fin (n + 1)) K)
  set N := adjoin k (Set.range (algebraMap K Ω) ∪
      Set.range (fun i => algebraMap (MvPolynomial (Fin (n + 1)) K) Ω (MvPolynomial.X i)))
  have hpoly : ∀ p : MvPolynomial (Fin (n + 1)) K, algebraMap _ Ω p ∈ N := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact subset_adjoin k _ (Or.inl ⟨a, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (subset_adjoin k _ (Or.inr ⟨i, rfl⟩))
  rw [eq_top_iff]
  intro z _
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin (n + 1)) K) z
  exact div_mem (hpoly p) (hpoly q)

end Omega

section ChangeVar

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {n : ℕ}

theorem transcendental_shift (x : Fin (n + 1) → Ω) (ξ δ : Ω)
    (hind : AlgebraicIndependent k (Fin.snoc (Fin.snoc x ξ) δ)) {a₁ a₂ : k} (hne : a₁ ≠ a₂) :
    Transcendental (adjoin k (Set.range x ∪ {ξ + algebraMap k Ω a₁ * δ}))
      (ξ + algebraMap k Ω a₂ * δ) := by
  classical
  set v : Fin (n + 3) → Ω := Fin.snoc (Fin.snoc x ξ) δ with hv
  set iξ : Fin (n + 3) := (Fin.last (n + 1)).castSucc with hiξ
  set iδ : Fin (n + 3) := Fin.last (n + 2) with hiδ
  have hvξ : v iξ = ξ := by simp [hv, hiξ]
  have hvδ : v iδ = δ := by simp [hv, hiδ]
  have hvx : ∀ i : Fin (n + 1), v i.castSucc.castSucc = x i := by intro i; simp [hv]
  set e : k := (a₂ - a₁)⁻¹ with he
  have hsub : a₂ - a₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hee : (a₂ - a₁) * e = 1 := mul_inv_cancel₀ hsub

  let X : Fin (n + 3) → MvPolynomial (Fin (n + 3)) k := MvPolynomial.X
  let C : k →+* MvPolynomial (Fin (n + 3)) k := MvPolynomial.C
  set f : Fin (n + 3) → MvPolynomial (Fin (n + 3)) k :=
    Fin.snoc (Fin.snoc (fun i : Fin (n + 1) => X i.castSucc.castSucc)
      (X iξ + C a₁ * X iδ)) (X iξ + C a₂ * X iδ) with hf
  set g : Fin (n + 3) → MvPolynomial (Fin (n + 3)) k :=
    Fin.snoc (Fin.snoc (fun i : Fin (n + 1) => X i.castSucc.castSucc)
      (C (a₂ * e) * X iξ - C (a₁ * e) * X iδ)) (C e * (X iδ - X iξ)) with hg
  have hfx : ∀ i : Fin (n + 1), f i.castSucc.castSucc = X i.castSucc.castSucc := by
    intro i; simp [hf]
  have hfξ : f iξ = X iξ + C a₁ * X iδ := by simp [hf, hiξ]
  have hfδ : f iδ = X iξ + C a₂ * X iδ := by simp [hf, hiδ]
  have hgx : ∀ i : Fin (n + 1), g i.castSucc.castSucc = X i.castSucc.castSucc := by
    intro i; simp [hg]
  have hgξ : g iξ = C (a₂ * e) * X iξ - C (a₁ * e) * X iδ := by simp [hg, hiξ]
  have hgδ : g iδ = C e * (X iδ - X iξ) := by simp [hg, hiδ]
  have heC : C a₂ * C e - C a₁ * C e = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, ← sub_mul, hee, map_one]
  have hcomp : (MvPolynomial.aeval g).comp (MvPolynomial.aeval f) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.id_apply]
    induction i using Fin.lastCases with
    | last =>
      change MvPolynomial.aeval g (f iδ) = X iδ
      rw [hfδ, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hgξ, hgδ, map_mul, map_mul]
      linear_combination (X iδ) * heC
    | cast j =>
      induction j using Fin.lastCases with
      | last =>
        change MvPolynomial.aeval g (f iξ) = X iξ
        rw [hfξ, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
          MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hgξ, hgδ, map_mul, map_mul]
        linear_combination (X iξ) * heC
      | cast j =>
        rw [hfx, MvPolynomial.aeval_X, hgx]
  have hfind : AlgebraicIndependent k f := by
    change Function.Injective (MvPolynomial.aeval f)
    intro p q hpq
    have := congrArg (MvPolynomial.aeval g) hpq
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp, AlgHom.id_apply,
      AlgHom.id_apply] at this
  have hnew := hind.aeval_of_algebraicIndependent hfind

  set v' : Fin (n + 3) → Ω := fun i => MvPolynomial.aeval v (f i) with hv'
  have hv'x : ∀ i : Fin (n + 1), v' i.castSucc.castSucc = x i := by
    intro i; rw [hv']; dsimp only; rw [hfx, MvPolynomial.aeval_X, hvx]
  have hv'ξ : v' iξ = ξ + algebraMap k Ω a₁ * δ := by
    rw [hv']; dsimp only
    rw [hfξ, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, hvξ, hvδ]
  have hv'δ : v' iδ = ξ + algebraMap k Ω a₂ * δ := by
    rw [hv']; dsimp only
    rw [hfδ, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, hvξ, hvδ]
  have hnew' : AlgebraicIndependent k v' := hnew
  have htr : Transcendental (Algebra.adjoin k (v' '' {iδ}ᶜ)) (v' iδ) :=
    hnew'.transcendental_adjoin (s := {iδ}ᶜ) (i := iδ) (by simp)
  rw [hv'δ] at htr
  have htr' : Transcendental (IntermediateField.adjoin k (v' '' {iδ}ᶜ))
      (ξ + algebraMap k Ω a₂ * δ) :=
    IntermediateField.transcendental_adjoin_iff.mpr htr
  apply transcendental_of_le' _ htr'
  apply adjoin.mono
  rintro z (⟨i, rfl⟩ | rfl)
  · refine ⟨i.castSucc.castSucc, ?_, hv'x i⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hiδ]
    exact ne_of_lt (Fin.castSucc_lt_last _)
  · refine ⟨iξ, ?_, hv'ξ⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hiδ, hiξ]
    exact ne_of_lt (Fin.castSucc_lt_last _)

end ChangeVar

section Final

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

local notation3 "Ωf[" K' ", " m "]" => FractionRing (MvPolynomial (Fin (m + 1)) K')

theorem transcendental_restrictScalars_adjoin {L : Type*} [Field L] [Algebra k L]
    {E : IntermediateField k L} {θ t : L} (hθ : IsIntegral E θ)
    (ht : Transcendental E t) : Transcendental ((adjoin E {θ}).restrictScalars k) t := by
  change Transcendental (adjoin E {θ}) t
  intro halg
  haveI : FiniteDimensional E (adjoin E {θ}) := adjoin.finiteDimensional hθ
  haveI : Algebra.IsIntegral E (adjoin E {θ}) := Algebra.IsIntegral.of_finite _ _
  have hint : IsIntegral E t := isIntegral_trans (R := E) _ halg.isIntegral
  exact ht hint.isAlgebraic

variable [Infinite k]

theorem fieldBertini
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {n : ℕ} (g : Fin (n + 1) → K) (c : Fin (n + 1) → k)
    (x : Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hx : ∀ i, x i = algebraMap (MvPolynomial (Fin (n + 1)) K) _ (MvPolynomial.X i))
    (hind : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc x (∑ i, algebraMap K _ (g i) * x i)) (algebraMap K _ (∑ i, c i • g i))))
    (θ : FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hθ : IsSeparable
      (IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i})) θ) :
    θ ∈ IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i}) := by
  classical

  set φK : K →+* Ωf[K, n] := algebraMap K Ωf[K, n] with hφK
  set ξ : Ωf[K, n] := ∑ i, φK (g i) * x i with hξ
  set δ : Ωf[K, n] := φK (∑ i, c i • g i) with hδ
  have hδ' : δ = ∑ i, algebraMap k Ωf[K, n] (c i) * φK (g i) := by
    rw [hδ, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def, map_mul, hφK, ← IsScalarTower.algebraMap_apply]
  set K₀ : IntermediateField k Ωf[K, n] := adjoin k (Set.range x) with hK₀
  set K₁ : IntermediateField k Ωf[K, n] := adjoin k (Set.range x ∪ {ξ}) with hK₁
  set K₂ : IntermediateField k Ωf[K, n] := adjoin k (Set.range x ∪ {ξ} ∪ {δ}) with hK₂

  have hxK₀ : ∀ i, x i ∈ K₀ := fun i => subset_adjoin k _ ⟨i, rfl⟩
  have hK₀K₂ : K₀ ≤ K₂ := adjoin.mono k _ _ (fun z hz => Or.inl (Or.inl hz))
  have hξK₂ : ξ ∈ K₂ := subset_adjoin k _ (Or.inl (Or.inr rfl))
  have hδK₂ : δ ∈ K₂ := subset_adjoin k _ (Or.inr rfl)

  have hxK : AlgebraicIndependent K x := by
    have h0 := (MvPolynomial.algebraicIndependent_X (Fin (n + 1)) K).map
      (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin (n + 1)) K) Ωf[K, n])
      (IsFractionRing.injective (MvPolynomial (Fin (n + 1)) K) Ωf[K, n]).injOn
    convert h0 using 1
    funext i; exact hx i

  have hxfun : (fun i => algebraMap (MvPolynomial (Fin (n + 1)) K) Ωf[K, n] (MvPolynomial.X i)) = x :=
    (funext hx).symm
  have htop : adjoin k (Set.range φK ∪ Set.range x) = ⊤ := by
    have := adjoin_range_union_range_X_eq_top k K n
    rwa [hxfun] at this

  have hK₀sc : SepClosedIn K₀ ⊤ := by
    have := sepClosedIn_adjoin_range (k := k) (L := Ωf[K, n]) K hsc x hxK
    rwa [htop] at this

  let σ : k → (Ωf[K, n] ≃ₐ[k] Ωf[K, n]) := fun a => sigma k K n (fun i => algebraMap k K (a * c i))
  have hσx : ∀ a i, σ a (x i) = x i + algebraMap k Ωf[K, n] (a * c i) := by
    intro a i
    rw [hx i]
    change sigma k K n _ _ = _
    rw [sigma_X, ← IsScalarTower.algebraMap_apply]
  have hσK : ∀ a (z : K), σ a (φK z) = φK z := fun a z => sigma_algebraMap_K k K n _ z
  set ξ_ : k → Ωf[K, n] := fun a => ξ + algebraMap k Ωf[K, n] a * δ with hξ_
  have hσξ : ∀ a, σ a ξ = ξ_ a := by
    intro a
    rw [hξ_]; dsimp only
    rw [hξ, map_sum, hδ', Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, hσK, hσx, map_mul]
    ring
  set θ_ : k → Ωf[K, n] := fun a => σ a θ with hθ_
  set K₁' : k → IntermediateField k Ωf[K, n] := fun a => adjoin k (Set.range x ∪ {ξ_ a}) with hK₁'
  have hK₁map : ∀ a, K₁.map (σ a : Ωf[K, n] →ₐ[k] Ωf[K, n]) = K₁' a := fun a =>
    map_adjoin_range_union_singleton (σ a) x (fun i => a * c i) (hσx a) ξ (ξ_ a) (hσξ a)
  have hθsep : ∀ a, IsSeparable (K₁' a) (θ_ a) := by
    intro a
    have h1 : IsSeparable (K₁.map (σ a : Ωf[K, n] →ₐ[k] Ωf[K, n])) (σ a θ) :=
      isSeparable_transport (intermediateFieldMap (σ a) K₁).toRingEquiv
        (σ a : Ωf[K, n] →+* Ωf[K, n]) (fun r => rfl) hθ
    rw [hK₁map] at h1
    exact h1
  have hξ_K₂ : ∀ a, ξ_ a ∈ K₂ := fun a =>
    add_mem hξK₂ (mul_mem (IntermediateField.algebraMap_mem _ _) hδK₂)
  have hK₁'le : ∀ a, K₁' a ≤ K₂ := by
    intro a
    apply adjoin_le_iff.mpr
    rintro z (⟨i, rfl⟩ | rfl)
    · exact hK₀K₂ (hxK₀ i)
    · exact hξ_K₂ a
  have hθsepK₂ : ∀ a, IsSeparable K₂ (θ_ a) := fun a => isSeparable_of_le (hK₁'le a) (hθsep a)

  have hfgK₂ : (⊤ : IntermediateField K₂ Ωf[K, n]).FG :=
    fg_top_of_adjoin_eq_top hfg htop K₂ (by rintro _ ⟨i, rfl⟩; exact hK₀K₂ (hxK₀ i))
  obtain ⟨a₁, a₂, hne, hadj⟩ := exists_ne_adjoin_simple_eq hfgK₂ θ_ hθsepK₂

  have htrans : Transcendental (K₁' a₁) (ξ_ a₂) := transcendental_shift x ξ δ hind hne
  set E₁ : IntermediateField k Ωf[K, n] := K₁' a₁ with hE₁
  set M : IntermediateField k Ωf[K, n] := (adjoin E₁ {θ_ a₁}).restrictScalars k with hM
  have hMtrans : Transcendental M (ξ_ a₂) :=
    transcendental_restrictScalars_adjoin (hθsep a₁).isIntegral htrans
  have hE₁M : E₁ ≤ M := fun z hz =>
    IntermediateField.algebraMap_mem (adjoin E₁ {θ_ a₁}) ⟨z, hz⟩
  have hK₀E₁ : K₀ ≤ E₁ := adjoin.mono k _ _ Set.subset_union_left
  have hK₀M : K₀ ≤ M := hK₀E₁.trans hE₁M
  have hscM : SepClosedIn K₀ M := hK₀sc.mono_right le_top
  have hres := hscM.adjoin_transcendental hK₀M hMtrans

  have hleft : (adjoin K₀ {ξ_ a₂}).restrictScalars k = K₁' a₂ := by
    rw [hK₀, adjoin_adjoin_left]
  have hθ₁M : θ_ a₁ ∈ M := mem_adjoin_simple_self E₁ (θ_ a₁)
  have hright : θ_ a₂ ∈ (adjoin M {ξ_ a₂}).restrictScalars k := by
    rw [restrictScalars_adjoin]

    have h1 : θ_ a₂ ∈ (adjoin K₂ {θ_ a₁}).restrictScalars k := by
      rw [mem_restrictScalars, hadj]; exact mem_adjoin_simple_self K₂ _
    rw [restrictScalars_adjoin, hK₂, adjoin_coe_adjoin_union] at h1
    refine (adjoin_le_iff.mpr ?_) h1

    set N : IntermediateField k Ωf[K, n] := adjoin k ((M : Set Ωf[K, n]) ∪ {ξ_ a₂}) with hN
    have hMN : M ≤ N := fun z hz => subset_adjoin k _ (Or.inl hz)
    have hξ₁N : ξ_ a₁ ∈ N := hMN (hE₁M (subset_adjoin k _ (Or.inr rfl)))
    have hξ₂N : ξ_ a₂ ∈ N := subset_adjoin k _ (Or.inr rfl)
    obtain ⟨hξN, hδN⟩ := mem_of_two_shifts N hne hξ₁N hξ₂N
    rintro z (((⟨i, rfl⟩ | rfl) | rfl) | rfl)
    · exact hMN (hK₀M (hxK₀ i))
    · exact hξN
    · exact hδN
    · exact hMN hθ₁M
  have hsep₂ : IsSeparable ((adjoin K₀ {ξ_ a₂}).restrictScalars k) (θ_ a₂) := by
    rw [hleft]; exact hθsep a₂
  have hfinal := hres (θ_ a₂) hright hsep₂
  rw [hleft, ← hK₁map] at hfinal
  obtain ⟨z, hz, hzθ⟩ := (IntermediateField.mem_map K₁).mp hfinal
  have : z = θ := (σ a₂).injective hzθ
  rw [← this]
  exact hz

end Final

end P2mFieldBertini
p2m_reactivate "P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini"

universe u v

theorem solution
    {k : Type u} {K : Type v} [Field k] [Infinite k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {n : ℕ} (g : Fin (n + 1) → K) (c : Fin (n + 1) → k)
    (x : Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hx : ∀ i, x i = algebraMap (MvPolynomial (Fin (n + 1)) K) _ (MvPolynomial.X i))
    (hind : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc x (∑ i, algebraMap K _ (g i) * x i)) (algebraMap K _ (∑ i, c i • g i))))
    (θ : FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hθ : IsSeparable
      (IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i})) θ) :
    θ ∈ IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i}) :=
  P2mFieldBertini.fieldBertini hfg hsc g c x hx hind θ hθ

end S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
end P2MW
export P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent (solution)
