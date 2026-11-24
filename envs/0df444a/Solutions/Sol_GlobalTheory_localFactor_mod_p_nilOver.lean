-- Prove2me | solution 1 for GlobalTheory.localFactor_mod_p_nilOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:18:47.794809+00:00
-- url     : https://prove2.me/submissions/79124bdb-8c29-4705-81af-a179908cbc3f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LocalFactorModPNilOver
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_quot_nontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
open TensorProduct IsLocalRing Matrix in
private theorem exists_localFactor_lemma {R₀ : Type} [CommRing R₀] {O R K A : _root_.ReciprocityTheory.PGsh.LAlg R₀}
    (q : _root_.ReciprocityTheory.PGsh.LHom O R) (hq : Function.Surjective q.1) (c : O.carrier)
    (hker : RingHom.ker (q.1 : O.carrier →+* R.carrier) = Ideal.span {c})
    (ρ : _root_.ReciprocityTheory.PGsh.LHom R K) (hρ : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρ) (hK : maximalIdeal K.carrier = ⊥)
    (s : _root_.ReciprocityTheory.PGsh.LHom O A) (hfin : (s.1 : O.carrier →+* A.carrier).Finite)
    (φ₀ : _root_.ReciprocityTheory.PGsh.LHom A O) (hφ₀ : φ₀.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O) :
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom A Λ) (j : _root_.ReciprocityTheory.PGsh.LHom R Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = ρ ∧ μ.comp s = j.comp q ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ R, ψ.comp μ = q.comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id R ∧ ρ.comp ψ = ρΛ := by
  classical
  have hmR : ∀ x ∈ maximalIdeal R.carrier, IsNilpotent x := by
    intro x hx
    apply hρ.2
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) x ∈ maximalIdeal K.carrier := map_nonunit _ x hx
    rw [hK] at h1
    exact h1
  have hc0 : q.1 c = 0 := by
    have h1 : c ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := hker ▸ Ideal.mem_span_singleton_self c
    exact h1
  have hc : ¬ IsUnit c := by
    intro hu
    have h1 := hu.map q.1
    rw [hc0] at h1
    exact not_isUnit_zero h1
  have hsc : ¬ IsUnit (s.1 c) := by
    haveI := s.2
    exact fun h => hc ((isUnit_map_iff (s.1 : O.carrier →+* A.carrier) c).1 h)
  set I : Ideal A.carrier := Ideal.span {s.1 c} with hI
  have hItop : I ≠ ⊤ := by
    rw [hI, Ne, Ideal.span_singleton_eq_top]
    exact hsc
  haveI : Nontrivial (A.carrier ⧸ I) := _root_.ReciprocityTheory.PGsh.Ainf.quot_nontrivial I hItop
  haveI : IsLocalRing (A.carrier ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀ := _root_.ReciprocityTheory.PGsh.LAlg.mk (A.carrier ⧸ I)
  let μ : _root_.ReciprocityTheory.PGsh.LHom A Λ := ⟨Ideal.Quotient.mkₐ R₀ I,
    _root_.ReciprocityTheory.PGsh.TowerExample.isLocalHom_of_surj ((Ideal.Quotient.mkₐ R₀ I : A.carrier →ₐ[R₀] A.carrier ⧸ I) : A.carrier →+* A.carrier ⧸ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I)⟩
  have hqc : ∀ a ∈ RingHom.ker q.1, ((Ideal.Quotient.mkₐ R₀ I).comp s.1) a = 0 := by
    intro a ha
    have ha' : a ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := ha
    rw [hker, Ideal.mem_span_singleton'] at ha'
    obtain ⟨b, rfl⟩ := ha'
    rw [AlgHom.comp_apply, map_mul, map_mul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), mul_zero]
  let j₀ : R.carrier →ₐ[R₀] A.carrier ⧸ I :=
    (Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc).comp
      (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom
  have hj₀ : ∀ x, j₀ (q.1 x) = Ideal.Quotient.mk I (s.1 x) := by
    intro x
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x) =
        Ideal.Quotient.mk (RingHom.ker q.1) x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc
      ((Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x)) = _
    rw [h1]
    rfl
  have hj₀loc : IsLocalHom (j₀ : R.carrier →+* A.carrier ⧸ I) := by
    constructor
    intro x hx
    by_contra hxu
    obtain ⟨n, hn⟩ := hmR x ((mem_maximalIdeal x).2 hxu)
    have h1 : IsUnit ((j₀ : R.carrier →+* A.carrier ⧸ I) x ^ n) := hx.pow n
    rw [← map_pow, hn, map_zero] at h1
    exact not_isUnit_zero h1
  let j : _root_.ReciprocityTheory.PGsh.LHom R Λ := ⟨j₀, hj₀loc⟩
  have hψI : ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → ∀ a ∈ I, (q.1.comp φ.1) a = 0 := by
    intro φ hφ a ha
    rw [hI, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    have h1 : φ.1 (s.1 c) = c := congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O O => f.1 c) hφ
    rw [AlgHom.comp_apply, map_mul, map_mul, h1, hc0, mul_zero]
  let ψ₀ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → (A.carrier ⧸ I →ₐ[R₀] R.carrier) :=
    fun φ hφ => Ideal.Quotient.liftₐ I (q.1.comp φ.1) (hψI φ hφ)
  have hψ₀mk : ∀ φ hφ a, ψ₀ φ hφ (Ideal.Quotient.mk I a) = q.1 (φ.1 a) := fun _ _ _ => rfl
  have hψ₀loc : ∀ φ hφ, IsLocalHom (ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) := by
    intro φ hφ
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : IsUnit (q.1 (φ.1 a)) := hx
    haveI := q.2
    haveI := φ.2
    have h2 : IsUnit (φ.1 a) := isUnit_of_map_unit (q.1 : O.carrier →+* R.carrier) _ h1
    have h3 : IsUnit a := isUnit_of_map_unit (φ.1 : A.carrier →+* O.carrier) _ h2
    exact h3.map (Ideal.Quotient.mk I)
  let ψ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → _root_.ReciprocityTheory.PGsh.LHom Λ R :=
    fun φ hφ => ⟨ψ₀ φ hφ, hψ₀loc φ hφ⟩
  have hψj : ∀ φ hφ r, ψ₀ φ hφ (j₀ r) = r := by
    intro φ hφ r
    obtain ⟨x, rfl⟩ := hq r
    rw [hj₀, hψ₀mk φ hφ]
    exact congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O R => f.1 x)
      (show q.comp (φ.comp s) = q.comp (_root_.ReciprocityTheory.PGsh.LHom.id O) by rw [hφ])
  have hkerm : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = 0 →
      l ∈ maximalIdeal (A.carrier ⧸ I) := by
    intro φ hφ l hl
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (ρ.1 (ψ₀ φ hφ l)) := (hu.map (ψ₀ φ hφ)).map ρ.1
    rw [hl] at h1
    exact not_isUnit_zero h1
  have hmK : ∀ φ hφ (l : A.carrier ⧸ I), l ∈ maximalIdeal (A.carrier ⧸ I) →
      ρ.1 (ψ₀ φ hφ l) = 0 := by
    intro φ hφ l hl
    haveI := hψ₀loc φ hφ
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) ((ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) l) ∈
        maximalIdeal K.carrier :=
      map_nonunit _ _ (map_nonunit _ l hl)
    rw [hK] at h1
    exact h1
  have hagree : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = ρ.1 (ψ₀ φ₀ hφ₀ l) := by
    intro φ hφ l
    have h1 : ρ.1 (ψ₀ φ₀ hφ₀ (l - j₀ (ψ₀ φ₀ hφ₀ l))) = 0 := by
      rw [map_sub, hψj φ₀ hφ₀ (ψ₀ φ₀ hφ₀ l), sub_self, map_zero]
    have h2 := hmK φ hφ _ (hkerm φ₀ hφ₀ _ h1)
    rw [map_sub, map_sub, hψj φ hφ (ψ₀ φ₀ hφ₀ l), sub_eq_zero] at h2
    exact h2
  have hcomp : (Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier) =
      (j₀ : R.carrier →+* A.carrier ⧸ I).comp (q.1 : O.carrier →+* R.carrier) := by
    ext x
    exact (hj₀ x).symm
  have hint : ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier)).IsIntegral :=
    ((RingHom.Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).comp
      hfin).to_isIntegral
  refine ⟨Λ, μ, j, ρ.comp (ψ φ₀ hφ₀), ⟨fun k => ?_, fun l hl => ?_⟩,
    Ideal.Quotient.mkₐ_surjective R₀ I, ?_, ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := hρ.1 k
    refine ⟨j₀ r, ?_⟩
    show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
    rw [hψj φ₀ hφ₀ r]
  · have hl' : ρ.1 (ψ₀ φ₀ hφ₀ l) = 0 := hl
    have hm := hkerm φ₀ hφ₀ l hl'
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hJR : J.comap (j₀ : R.carrier →+* A.carrier ⧸ I) = maximalIdeal R.carrier := by
      have hP : (J.comap (j₀ : R.carrier →+* A.carrier ⧸ I)).IsPrime := Ideal.comap_isPrime _ J
      apply le_antisymm
      · exact le_maximalIdeal hP.ne_top
      · intro x hx
        obtain ⟨n, hn⟩ := hmR x hx
        exact hP.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)
    have hmax : (J.comap ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier))).IsMaximal := by
      rw [hcomp, ← Ideal.comap_comap, hJR]
      exact Ideal.comap_isMaximal_of_surjective (q.1 : O.carrier →+* R.carrier) hq
    have hJmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hint J hmax
    rw [eq_maximalIdeal hJmax]
    exact hm
  · exact Subtype.ext (AlgHom.ext fun r => by
      show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
      rw [hψj φ₀ hφ₀ r])
  · exact Subtype.ext (AlgHom.ext fun x => by
      show Ideal.Quotient.mk I (s.1 x) = j₀ (q.1 x)
      exact (hj₀ x).symm)
  · intro φ hφ
    refine ⟨ψ φ hφ, Subtype.ext (AlgHom.ext fun a => rfl),
      Subtype.ext (AlgHom.ext fun r => hψj φ hφ r), Subtype.ext (AlgHom.ext fun l => hagree φ hφ l)⟩
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
open TensorProduct IsLocalRing Matrix
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Λ) (j : _root_.ReciprocityTheory.PGsh.LHom (Tw.R 0) Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ D.K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D hg
  have hid : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver (_root_.ReciprocityTheory.PGsh.LHom.id D.K) :=
    ⟨fun x => ⟨x, rfl⟩, fun a ha => ⟨1, by rw [pow_one]; exact (RingHom.mem_ker).1 ha⟩⟩
  have hK : maximalIdeal (D.K : Type) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hsub : ∀ u v : {x // (B.map (_root_.ReciprocityTheory.PGsh.LHom.id D.K)) x = 0}, u = v := by
      intro u v
      have hu := u.2
      have hv := v.2
      rw [B.map_id] at hu hv
      exact Subtype.ext (hu.trans hv.symm)
    have h1 : (fun _ : Fin g => (⟨a, ha⟩ : maximalIdeal (D.K : Type))) = fun _ => 0 :=
      (D.ch.χ (_root_.ReciprocityTheory.PGsh.LHom.id D.K) hid).symm.injective (hsub _ _)
    have h2 := congrFun h1 ⟨0, hg⟩
    exact (Ideal.mem_bot).2 (congrArg Subtype.val h2)
  have hW := D.sm.nil
  have heq := D.wd.ρW_eq
  have hρ1 : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 := by
    refine ⟨fun k => ?_, fun a ha => ?_⟩
    · obtain ⟨w, hw⟩ := hW.1 k
      refine ⟨D.wd.πW.1 w, ?_⟩
      rw [← hw, ← heq]
      rfl
    · obtain ⟨w, rfl⟩ := D.wd.πW_surj a
      have hw : w ∈ RingHom.ker (D.wd.ρW.1 : D.wd.W.carrier →+* D.K.carrier) := by
        rw [RingHom.mem_ker, ← heq]
        exact (RingHom.mem_ker).1 ha
      exact (hW.2 w hw).map (D.wd.πW.1 : D.wd.W.carrier →+* (Tw.R 0).carrier)
  refine ⟨hK, hρ1, fun i => ?_⟩
  have hsec : ∃ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : (D.fin.AAx i).carrier) = 0 := D.fin.sep i 1 fun φ hφ => absurd hφ (hne φ)
    exact one_ne_zero h1
  obtain ⟨φ₀, hφ₀⟩ := hsec
  have hfin : ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).Finite := by
    letI : Algebra Tw.O.carrier (D.fin.AAx i).carrier :=
      ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
    exact (D.fin.free i).2
  exact exists_localFactor_lemma (Tw.q 0) D.tower_zero_surjective (p : Tw.O.carrier) D.tower_zero_ker D.wd.ρ1 hρ1 hK
    (D.fin.sO i) hfin φ₀ hφ₀
end _root_.GlobalTheory
end GlobalTheory
