-- Prove2me | solution 1 for HopfAlgebra.free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/56c994b1-88b6-50ec-a757-2447e1ed64ca

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
import Theorems.Thm_AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false

p2m_open "AlgebraicGeometry CategoryTheory Coalgebra CategoryTheory.Coalgebra"
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

universe u v

namespace P2mCharGroupRank

section Plumbing

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [Algebra k H] (h : ℕ)
  (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H))

include hsm

theorem smoothOfRelativeDimension_specMap :
    SmoothOfRelativeDimension h (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
  (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension h)).mpr hsm

theorem finiteType : Algebra.FiniteType k H := by
  haveI := smoothOfRelativeDimension_specMap k H h hsm
  haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    SmoothOfRelativeDimension.smooth h _
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k H))) := inferInstance
  have hft : RingHom.FiniteType (algebraMap k H) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  exact RingHom.finiteType_algebraMap.mp hft

theorem isReduced : IsReduced H := by
  haveI := smoothOfRelativeDimension_specMap k H h hsm
  haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    SmoothOfRelativeDimension.smooth h _
  have := AlgebraicGeometry.isReduced_of_smooth_of_field (Spec.map (CommRingCat.ofHom (algebraMap k H)))
  exact (affine_isReduced_iff (CommRingCat.of H)).mp this

theorem ringKrullDim_le : ringKrullDim H ≤ h := by
  haveI := smoothOfRelativeDimension_specMap k H h hsm
  have := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
    (Spec.map (CommRingCat.ofHom (algebraMap k H))) h
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact this

end Plumbing

theorem eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot {R : Type u} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (h : PrimeSpectrum.basicOpen e = ⊥) : e = 0 := by
  obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff e).mp h
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero] at hn
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    · exact absurd hn one_ne_zero
  · have : e ^ (n - 1 + 1) = 0 := by rw [Nat.sub_add_cancel hpos]; exact hn
    rwa [he.pow_succ_eq] at this

theorem eq_zero_or_eq_one_of_isIdempotentElem {R : Type u} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hclopen : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hclopen with h | h
  · left
    exact eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot he (TopologicalSpace.Opens.ext h)
  · right
    have h1 : PrimeSpectrum.basicOpen (1 - e) = ⊥ := by
      apply TopologicalSpace.Opens.ext
      change (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) = ∅
      rw [← PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he]
      have h2 : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) =
          (PrimeSpectrum.zeroLocus {e})ᶜ := PrimeSpectrum.basicOpen_eq_zeroLocus_compl e
      rw [h2] at h

      have := congrArg compl h
      simpa using this
    have := eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot he.one_sub h1
    exact (sub_eq_zero.mp this).symm

theorem nontrivial_of_hopf (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] :
    Nontrivial H :=
  ⟨⟨0, 1, fun h => (zero_ne_one (α := k)) (by
    simpa using congrArg (Coalgebra.counit (R := k) (A := H)) h)⟩⟩

section Hopf

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

theorem linearIndependent_pow_of_orderOf (g : GroupLike k H) :
    LinearIndependent k (fun i : Fin (orderOf g) => (g ^ (i : ℕ)).val) := by
  have hinj : Function.Injective (fun i : Fin (orderOf g) => g ^ (i : ℕ)) := by
    intro i j hij
    apply Fin.ext
    have := pow_inj_mod.mp hij
    rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
  exact (linearIndep_groupLikeVal (R := k) (A := H)).comp _ hinj

theorem orderOf_ne_of_cast_eq_zero [IsReduced H] (g : GroupLike k H) {q : ℕ} (hq : q.Prime)
    (hqk : (q : k) = 0) : orderOf g ≠ q := by
  intro hord

  haveI : Fact q.Prime := ⟨hq⟩
  have hchar : CharP k q := by
    have := (CharP.cast_eq_zero_iff k (ringChar k) q).mp hqk
    rcases (Nat.dvd_prime hq).mp this with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · exact h1 ▸ (inferInstance : CharP k (ringChar k))
  haveI : Nontrivial H := nontrivial_of_hopf k H
  haveI : CharP H q := charP_of_injective_algebraMap (algebraMap k H).injective q
  have hpow : g.val ^ q = 1 := by
    have := pow_orderOf_eq_one g
    rw [hord] at this
    exact congrArg GroupLike.val this
  have hnil : IsNilpotent (g.val - 1) := ⟨q, by rw [sub_pow_char, hpow, one_pow, sub_self]⟩
  have h1 : g.val = 1 := sub_eq_zero.mp hnil.eq_zero
  have hg1 : g = 1 := GroupLike.ext h1
  rw [hg1, orderOf_one] at hord
  exact hq.one_lt.ne hord

theorem orderOf_ne_of_cast_ne_zero [ConnectedSpace (PrimeSpectrum H)] (g : GroupLike k H) {q : ℕ}
    (hq : q.Prime) (hqk : (q : k) ≠ 0) : orderOf g ≠ q := by
  intro hord
  haveI : Nontrivial H := nontrivial_of_hopf k H
  haveI : NeZero q := ⟨hq.ne_zero⟩
  let x : H := g.val
  have hxq : x ^ q = 1 := by
    have := pow_orderOf_eq_one g
    rw [hord] at this
    exact congrArg GroupLike.val this

  let s : H := ∑ i : Fin q, x ^ (i : ℕ)
  have hxs : ∀ j : Fin q, x ^ (j : ℕ) * s = s := by
    intro j
    simp only [s, Finset.mul_sum]

    have : ∀ i : Fin q, x ^ (j : ℕ) * x ^ (i : ℕ) = x ^ ((j + i : Fin q) : ℕ) := by
      intro i
      rw [← pow_add, Fin.val_add]
      conv_lhs => rw [← Nat.mod_add_div ((j : ℕ) + i) q, pow_add, pow_mul, hxq, one_pow, mul_one]
    simp_rw [this]
    exact Fintype.sum_equiv (Equiv.addLeft j) _ _ (fun i => rfl)
  have hss : s * s = (q : H) * s := by
    calc s * s = ∑ j : Fin q, x ^ (j : ℕ) * s := by rw [Finset.sum_mul]
      _ = ∑ _j : Fin q, s := Finset.sum_congr rfl fun j _ => hxs j
      _ = (q : H) * s := by simp
  have hqH : (q : H) ≠ 0 := by
    intro h0
    apply hqk
    apply (algebraMap k H).injective
    rw [map_natCast, h0, map_zero]
  haveI : Invertible (q : H) := invertibleOfNonzero (α := k) hqk |>.map (algebraMap k H) |>.copy _
    (by rw [map_natCast])
  let e : H := ⅟(q : H) * s
  have he : IsIdempotentElem e := by
    change ⅟(q : H) * s * (⅟(q : H) * s) = ⅟(q : H) * s
    calc ⅟(q : H) * s * (⅟(q : H) * s) = ⅟(q : H) * ⅟(q : H) * (s * s) := by ring
      _ = ⅟(q : H) * ⅟(q : H) * ((q : H) * s) := by rw [hss]
      _ = ⅟(q : H) * s := by
          rw [← mul_assoc, mul_assoc (⅟(q : H)), invOf_mul_self, mul_one]

  have hli := linearIndependent_pow_of_orderOf g
  rw [hord] at hli
  have hq1 : 1 < q := hq.one_lt
  rcases eq_zero_or_eq_one_of_isIdempotentElem he with h0 | h1
  ·
    have hs0 : s = 0 := by
      have := congrArg (fun y => (q : H) * y) h0
      simpa [e, ← mul_assoc, mul_invOf_self] using this
    have := (Fintype.linearIndependent_iff.mp hli) (fun _ => (1 : k)) (by
      simpa [one_smul] using hs0) ⟨0, hq.pos⟩
    exact one_ne_zero this
  ·
    have hs1 : s = (q : H) := by
      have := congrArg (fun y => (q : H) * y) h1
      simpa [e, ← mul_assoc, mul_invOf_self] using this
    let c : Fin q → k := fun i => if i = 0 then 1 - (q : k) else 1
    have hsum : ∑ i : Fin q, c i • x ^ (i : ℕ) = 0 := by
      have hsplit : ∀ i : Fin q, c i • x ^ (i : ℕ) =
          (1 : k) • x ^ (i : ℕ) - (if i = 0 then (q : k) • x ^ (i : ℕ) else 0) := by
        intro i
        by_cases hi : i = 0
        · simp only [c, if_pos hi, sub_smul]
        · simp only [c, if_neg hi, sub_zero]
      simp_rw [hsplit, Finset.sum_sub_distrib, one_smul]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_eq' Finset.univ (0 : Fin q),
        if_pos (Finset.mem_univ _), Finset.sum_singleton]
      change s - (q : k) • x ^ ((0 : Fin q) : ℕ) = 0
      rw [hs1, Fin.val_zero, pow_zero, Algebra.smul_def, mul_one, map_natCast, sub_self]
    have := (Fintype.linearIndependent_iff.mp hli) c hsum ⟨1, hq1⟩
    have hne : (⟨1, hq1⟩ : Fin q) ≠ 0 := fun h => absurd (congrArg Fin.val h) (by simp)
    simp only [c, if_neg hne] at this
    exact one_ne_zero this

theorem groupLike_eq_one_of_pow_eq_one [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    (g : GroupLike k H) {n : ℕ} (hn : 0 < n) (hg : g ^ n = 1) : g = 1 := by
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hg⟩
  have hne : orderOf g ≠ 0 := hfin.orderOf_pos.ne'
  by_contra hg1
  have hord1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hord1
  have hordq : orderOf (g ^ (orderOf g / q)) = q := orderOf_pow_orderOf_div hne hqd
  by_cases hqk : (q : k) = 0
  · exact orderOf_ne_of_cast_eq_zero _ hq hqk hordq
  · exact orderOf_ne_of_cast_ne_zero _ hq hqk hordq

theorem isMulTorsionFree [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] :
    IsMulTorsionFree (GroupLike k H) := by
  refine ⟨fun n hn a b hab => ?_⟩
  change a ^ n = b ^ n at hab

  have h : (a * b⁻¹) ^ n = 1 := by rw [mul_pow, hab, ← mul_pow, mul_inv_cancel, one_pow]
  have := groupLike_eq_one_of_pow_eq_one (a * b⁻¹) (Nat.pos_of_ne_zero hn) h
  exact mul_inv_eq_one.mp this

end Hopf

section GroupAlgebra

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]

abbrev CharLat : Type u := Additive (GroupLike k H)

variable {k H} in

def gl (m : CharLat k H) : H := (Additive.toMul m : GroupLike k H).val

noncomputable def inclHom : Multiplicative (CharLat k H) →* H where
  toFun x := gl (Multiplicative.toAdd x)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def φ : AddMonoidAlgebra k (CharLat k H) →ₐ[k] H :=
  AddMonoidAlgebra.lift k H (CharLat k H) (inclHom k H)

variable {k H}

theorem isGroupLikeElem_gl (m : CharLat k H) : IsGroupLikeElem k (gl m) :=
  (Additive.toMul m : GroupLike k H).2

theorem gl_add (m n : CharLat k H) : gl (m + n) = gl m * gl n := rfl

theorem gl_zero : gl (0 : CharLat k H) = 1 := rfl

theorem gl_neg (m : CharLat k H) : gl (-m) = HopfAlgebra.antipode k (gl m) := rfl

theorem φ_single (m : CharLat k H) (c : k) :
    φ k H (AddMonoidAlgebra.single m c) = c • gl m := by
  rw [φ, AddMonoidAlgebra.lift_single]
  rfl

theorem φ_apply (f : AddMonoidAlgebra k (CharLat k H)) :
    φ k H f = f.coeff.sum fun m c => c • gl m := by
  rw [φ, AddMonoidAlgebra.lift_apply]
  rfl

theorem φ_injective : Function.Injective (φ k H) := by
  have hli : LinearIndependent k (gl : CharLat k H → H) :=
    (linearIndep_groupLikeVal (R := k) (A := H)).comp _ Additive.toMul.injective
  intro f g hfg
  have : Finsupp.linearCombination k (gl : CharLat k H → H) f.coeff =
      Finsupp.linearCombination k (gl : CharLat k H → H) g.coeff := by
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, ← φ_apply, ← φ_apply]
    exact hfg
  exact AddMonoidAlgebra.coeff_injective (hli this)

variable (k H)

noncomputable def K : Subalgebra k H := (φ k H).range

variable {k H}

theorem mem_K_iff (x : H) : x ∈ K k H ↔ ∃ f : AddMonoidAlgebra k (CharLat k H), φ k H f = x :=
  AlgHom.mem_range _

theorem gl_mem (m : CharLat k H) : gl m ∈ K k H :=
  (mem_K_iff _).mpr ⟨AddMonoidAlgebra.single m 1, by rw [φ_single, one_smul]⟩

theorem comul_mem (x : H) (hx : x ∈ K k H) :
    comul (R := k) x ∈ Submodule.span k
      {t : H ⊗[k] H | ∃ a ∈ K k H, ∃ b ∈ K k H, t = a ⊗ₜ[k] b} := by
  obtain ⟨f, rfl⟩ := (mem_K_iff _).mp hx
  rw [φ_apply, map_finsuppSum]
  refine Submodule.sum_mem _ fun m _ => ?_
  dsimp only
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨gl m, gl_mem m, gl m, gl_mem m, (isGroupLikeElem_gl m).comul_eq_tmul_self⟩

theorem antipode_mem (x : H) (hx : x ∈ K k H) : HopfAlgebra.antipode k x ∈ K k H := by
  obtain ⟨f, rfl⟩ := (mem_K_iff _).mp hx
  rw [φ_apply, map_finsuppSum]
  refine Subalgebra.sum_mem _ fun m _ => ?_
  dsimp only
  rw [map_smul, ← gl_neg]
  exact Subalgebra.smul_mem _ (gl_mem (-m)) _

theorem faithfullyFlat_K [Algebra.FiniteType k H] : Module.FaithfullyFlat (K k H) H :=
  HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem (K k H)
    (comul_mem (k := k) (H := H)) (antipode_mem (k := k) (H := H))

def augI (S : Set (CharLat k H)) : Ideal H := Ideal.span ((fun m => gl m - 1) '' S)

theorem augI_mono {S T : Set (CharLat k H)} (h : S ⊆ T) : augI S ≤ augI T :=
  Ideal.span_mono (Set.image_mono h)

theorem sub_one_mem_augI {S : Set (CharLat k H)} {m : CharLat k H} (hm : m ∈ S) :
    gl m - 1 ∈ augI S :=
  Ideal.subset_span ⟨m, hm, rfl⟩

noncomputable def glK (m : CharLat k H) : K k H := ⟨gl m, gl_mem m⟩

noncomputable def augJ (S : Set (CharLat k H)) : Ideal (K k H) := Ideal.span ((fun m => glK m - 1) '' S)

theorem map_augJ (S : Set (CharLat k H)) :
    (augJ S).map (algebraMap (K k H) H) = augI S := by
  rw [augJ, Ideal.map_span, ← Set.image_comp]
  rfl

noncomputable def ψ (N : Submodule ℤ (CharLat k H)) :
    K k H →ₐ[k] AddMonoidAlgebra k (CharLat k H ⧸ N) :=
  (AddMonoidAlgebra.mapDomainAlgHom k k N.mkQ.toAddMonoidHom).comp
    (AlgEquiv.ofInjective (φ k H) φ_injective).symm.toAlgHom

theorem ψ_glK (N : Submodule ℤ (CharLat k H)) (m : CharLat k H) :
    ψ N (glK m) = AddMonoidAlgebra.single (N.mkQ m) 1 := by
  have h1 : (AlgEquiv.ofInjective (φ k H) φ_injective) (AddMonoidAlgebra.single m 1) = glK m := by
    apply Subtype.ext
    rw [AlgEquiv.ofInjective_apply, φ_single, one_smul]
    rfl
  have h2 : (AlgEquiv.ofInjective (φ k H) φ_injective).symm (glK m) = AddMonoidAlgebra.single m 1 := by
    rw [← h1, AlgEquiv.symm_apply_apply]
  change AddMonoidAlgebra.mapDomainAlgHom k k N.mkQ.toAddMonoidHom
    ((AlgEquiv.ofInjective (φ k H) φ_injective).symm (glK m)) = _
  rw [h2, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

theorem augJ_le_ker (N : Submodule ℤ (CharLat k H)) :
    augJ (N : Set (CharLat k H)) ≤ RingHom.ker (ψ N) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one]
  change ψ N (glK m) - 1 = 0
  rw [ψ_glK, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hm, AddMonoidAlgebra.one_def,
    sub_self]

theorem mem_of_sub_one_mem_augI [Algebra.FiniteType k H] (N : Submodule ℤ (CharLat k H))
    (m : CharLat k H) (hm : gl m - 1 ∈ augI (N : Set (CharLat k H))) : m ∈ N := by
  haveI := faithfullyFlat_K (k := k) (H := H)

  have hJ : glK m - 1 ∈ augJ (N : Set (CharLat k H)) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := H) (augJ (N : Set (CharLat k H))),
      Ideal.mem_comap, map_augJ, map_sub, map_one]
    exact hm

  have h0 : ψ N (glK m - 1) = 0 := augJ_le_ker N hJ
  rw [map_sub, map_one, ψ_glK, AddMonoidAlgebra.one_def, sub_eq_zero] at h0
  have : N.mkQ m = 0 :=
    (Finsupp.single_left_inj one_ne_zero).mp (by simpa using congrArg AddMonoidAlgebra.coeff h0)
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero N).mp this

theorem moduleFinite_charLat [Algebra.FiniteType k H] : Module.Finite ℤ (CharLat k H) := by
  haveI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let e : Submodule ℤ (CharLat k H) ↪o Ideal H :=
    OrderEmbedding.ofMapLEIff (fun N => augI (N : Set (CharLat k H))) fun N₁ N₂ =>
      ⟨fun h m hm => mem_of_sub_one_mem_augI N₂ m (h (sub_one_mem_augI hm)),
        fun h => augI_mono h⟩
  haveI : WellFoundedGT (Submodule ℤ (CharLat k H)) := e.strictMono.wellFoundedGT
  haveI : IsNoetherian ℤ (CharLat k H) := isNoetherian_mk inferInstance
  infer_instance

theorem ringKrullDim_le_of_faithfullyFlat (A : Type*) (B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] : ringKrullDim A ≤ ringKrullDim B := by
  haveI : Algebra.HasGoingDown A B := inferInstance
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨P, hP⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) l.last
  haveI : P.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [Ideal.under_def, ← hP]; rfl⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P.asIdeal
  calc (l.length : WithBot ℕ∞) = L.length := by rw [hlen]
    _ ≤ ⨆ (p : LTSeries (PrimeSpectrum B)), (p.length : WithBot ℕ∞) := le_iSup_iff.mpr fun b hb => hb L

theorem ringKrullDim_K [Module.Free ℤ (CharLat k H)] [Module.Finite ℤ (CharLat k H)] :
    ringKrullDim (K k H) = Module.finrank ℤ (CharLat k H) := by
  set r := Module.finrank ℤ (CharLat k H)
  let b : Module.Basis (Fin r) ℤ (CharLat k H) := Module.finBasis ℤ (CharLat k H)
  let e : CharLat k H ≃+ (Fin r → ℤ) := b.equivFun.toAddEquiv
  have h1 : ringKrullDim (K k H) = ringKrullDim (AddMonoidAlgebra k (CharLat k H)) :=
    ringKrullDim_eq_of_ringEquiv (AlgEquiv.ofInjective (φ k H) φ_injective).symm.toRingEquiv
  have h2 : ringKrullDim (AddMonoidAlgebra k (CharLat k H)) =
      ringKrullDim (AddMonoidAlgebra k (Fin r → ℤ)) :=
    ringKrullDim_eq_of_ringEquiv (AddMonoidAlgebra.domCongr k k e).toRingEquiv
  rw [h1, h2, AddMonoidAlgebra.ringKrullDim_pi_fin_int_eq]

theorem finrank_le_ringKrullDim [Algebra.FiniteType k H] [Module.Free ℤ (CharLat k H)]
    [Module.Finite ℤ (CharLat k H)] :
    (Module.finrank ℤ (CharLat k H) : WithBot ℕ∞) ≤ ringKrullDim H := by
  haveI := faithfullyFlat_K (k := k) (H := H)
  rw [← ringKrullDim_K (k := k) (H := H)]
  exact ringKrullDim_le_of_faithfullyFlat (K k H) H

end GroupAlgebra

end P2mCharGroupRank

open P2mCharGroupRank

theorem solution
    (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
    [ConnectedSpace (PrimeSpectrum H)] (h : ℕ)
    (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H)) :
    Module.Free ℤ (Additive (GroupLike k H)) ∧ Module.Finite ℤ (Additive (GroupLike k H)) ∧
      Module.finrank ℤ (Additive (GroupLike k H)) ≤ h := by
  haveI : Algebra.FiniteType k H := finiteType k H h hsm
  haveI : IsReduced H := isReduced k H h hsm
  haveI hfin : Module.Finite ℤ (CharLat k H) := moduleFinite_charLat
  haveI : IsMulTorsionFree (GroupLike k H) := isMulTorsionFree
  haveI hfree : Module.Free ℤ (CharLat k H) := Module.free_of_finite_type_torsion_free'
  refine ⟨hfree, hfin, ?_⟩
  have h1 := finrank_le_ringKrullDim (k := k) (H := H)
  have h2 := ringKrullDim_le k H h hsm
  exact_mod_cast h1.trans h2

end S_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
end P2MW
export P2MW.S_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension (solution)
