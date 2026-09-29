-- Prove2me | solution 1 for IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d51a49ee-7cdb-5df6-b280-3e5d7b79f6bc

import Mathlib
import Definitions.Def_Patching_SystemTypes
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Theorems.Thm_UniqueFactorizationMonoid_of_isLocalization_away_of_prime
import Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one
import Theorems.Thm_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
import Theorems.Thm_IsRegularLocalRing_depth_self_eq_ringKrullDim
import Theorems.Thm_RingTheory_Sequence_isWeaklyRegular_of_free
import Theorems.Thm_Module_depth_le_ringKrullDim
import Theorems.Thm_Module_depth_quotSMulTop_succ_eq
import Theorems.Thm_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing

set_option autoImplicit false

open IsLocalRing RingTheory.Sequence
open scoped TensorProduct

universe u v w

namespace P2mAB
namespace DepthLemma

variable {R : Type*} [CommRing R] [IsLocalRing R]

lemma length_le_depth {M : Type*} [AddCommGroup M] [Module R M] {rs : List R}
    (h1 : IsWeaklyRegular M rs) (h2 : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (rs.length : ℕ∞) ≤ Module.depth R M :=
  le_sSup ⟨rs, h1, h2, rfl⟩

lemma exists_isSMulRegular_of_one_le_depth {M : Type*} [AddCommGroup M] [Module R M]
    (h : 1 ≤ Module.depth R M) : ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hcon
  push Not at hcon
  have : Module.depth R M ≤ 0 := by
    apply sSup_le
    rintro _ ⟨rs, h1, h2, rfl⟩
    cases rs with
    | nil => simp
    | cons r rs =>
      exact absurd ((isWeaklyRegular_cons_iff M r rs).mp h1).1 (hcon r (h2 r (by simp)))
  exact absurd (h.trans this) (by simp)

lemma not_isAssociatedPrime_of_isSMulRegular [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    ¬ IsAssociatedPrime (maximalIdeal R) M := by
  intro h
  obtain ⟨m, hm⟩ := (isAssociatedPrime_iff.mp h).2
  have hxm : x • m = 0 := by
    have : x ∈ Submodule.colon ⊥ {m} := hm ▸ hx
    simpa [Submodule.mem_colon_singleton] using this
  have hm0 : m = 0 := hreg (by simpa using hxm)
  apply (maximalIdeal.isMaximal R).ne_top
  rw [hm, hm0]
  ext r
  simp [Submodule.mem_colon_singleton]

theorem core [IsNoetherianRing R] (n : ℕ) :
    ∀ {K F M : Type*} [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
      [Module.Finite R F] [AddCommGroup M] [Module R M]
      (f : K →ₗ[R] F) (g : F →ₗ[R] M), Function.Injective f → Function.Exact f g →
      Function.Surjective g →
      (n : ℕ∞) ≤ Module.depth R F → (n : ℕ∞) ≤ Module.depth R M + 1 →
      (n : ℕ∞) ≤ Module.depth R K := by
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro K F M _ _ _ _ _ _ _ f g hf hfg hg hF hM

    have hF1 : 1 ≤ Module.depth R F := le_trans (by simp) hF
    obtain ⟨x, hxm, hxF⟩ := exists_isSMulRegular_of_one_le_depth hF1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      have hxK : IsSMulRegular K x := hxF.of_injective f hf
      have h1 : IsWeaklyRegular K [x] := (isWeaklyRegular_singleton_iff K x).mpr hxK
      simpa using length_le_depth h1 (by simpa using hxm)
    ·
      haveI : Module.Finite R M := Module.Finite.of_surjective g hg
      have hM1 : 1 ≤ Module.depth R M := by
        have h1 : ((n : ℕ) : ℕ∞) + 1 ≤ Module.depth R M + 1 := by
          simpa [Nat.cast_succ] using hM
        have h2 : (n : ℕ∞) ≤ Module.depth R M := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h1
        exact le_trans (by exact_mod_cast hn) h2
      obtain ⟨y, hym, hyM⟩ := exists_isSMulRegular_of_one_le_depth hM1
      obtain ⟨z, hzm, hzF, hzM⟩ :=
        Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular F M
          (not_isAssociatedPrime_of_isSMulRegular hxm hxF)
          (not_isAssociatedPrime_of_isSMulRegular hym hyM)
      have hzK : IsSMulRegular K z := hzF.of_injective f hf

      let f' := QuotSMulTop.map z f
      let g' := QuotSMulTop.map z g
      have hf' : Function.Injective f' := by
        have h0 : Function.Exact (0 : K →ₗ[R] K) f := by
          intro k
          simp only [LinearMap.zero_apply, Set.mem_range, exists_const]
          constructor
          · intro hk
            exact (hf (by simpa using hk) : k = 0) ▸ rfl
          · rintro rfl; simp
        have := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h0 hfg hzM
        rw [map_zero] at this
        rw [← LinearMap.ker_eq_bot, this.linearMap_ker_eq]
        simp
      have hfg' : Function.Exact f' g' := QuotSMulTop.map_exact z hfg hg
      have hg' : Function.Surjective g' := QuotSMulTop.map_surjective z hg
      haveI : Module.Finite R (QuotSMulTop z F) :=
        inferInstanceAs (Module.Finite R (F ⧸ _))
      have hKf : Module.Finite R K := Module.Finite.of_injective f hf

      have eF := Module.depth_quotSMulTop_succ_eq F hzm hzF
      have eM := Module.depth_quotSMulTop_succ_eq M hzm hzM
      have eK := Module.depth_quotSMulTop_succ_eq K hzm hzK
      have hF' : (n : ℕ∞) ≤ Module.depth R (QuotSMulTop z F) := by
        have : ((n : ℕ) : ℕ∞) + 1 ≤ Module.depth R (QuotSMulTop z F) + 1 := by
          rw [eF]; simpa [Nat.cast_succ] using hF
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
      have hM' : (n : ℕ∞) ≤ Module.depth R (QuotSMulTop z M) + 1 := by
        rw [eM]
        have : ((n : ℕ) : ℕ∞) + 1 ≤ Module.depth R M + 1 := by simpa [Nat.cast_succ] using hM
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
      have hK' := ih f' g' hf' hfg' hg' hF' hM'
      rw [← eK]
      simpa [Nat.cast_succ] using add_le_add_right hK' 1

theorem min_depth_depth_add_one_le_depth_of_exact
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {K F M : Type*} [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    [Module.Finite R F] [AddCommGroup M] [Module R M]
    (f : K →ₗ[R] F) (g : F →ₗ[R] M) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    min (Module.depth R F) (Module.depth R M + 1) ≤ Module.depth R K := by

  rcases eq_or_ne (Module.depth R K) ⊤ with hK | hK
  · simp [hK]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hK
  by_contra hlt
  push Not at hlt
  rw [← hm] at hlt
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ min (Module.depth R F) (Module.depth R M + 1) := by
    have := (ENat.add_one_le_iff (ENat.coe_ne_top m)).mpr hlt
    simpa [Nat.cast_succ] using this
  have := core (R := R) (m + 1) f g hf hfg hg (h1.trans (min_le_left _ _))
    (h1.trans (min_le_right _ _))
  rw [← hm] at this
  have h2 : (m + 1 : ℕ) ≤ m := by exact_mod_cast this
  omega

end P2mAB.DepthLemma

namespace P2mAB
namespace StablyFree

def HasFFR (R : Type u) [CommRing R] : ℕ → (K : Type u) → [AddCommGroup K] → [Module R K] → Prop
  | 0, K, _, _ => Module.Finite R K ∧ Module.Free R K
  | n + 1, K, _, _ => ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] K),
      Function.Surjective f ∧ HasFFR R n (LinearMap.ker f)

variable {R : Type u} [CommRing R]

lemma hasFFR_zero_iff (K : Type u) [AddCommGroup K] [Module R K] :
    HasFFR R 0 K ↔ Module.Finite R K ∧ Module.Free R K := Iff.rfl

lemma hasFFR_succ_iff (n : ℕ) (K : Type u) [AddCommGroup K] [Module R K] :
    HasFFR R (n + 1) K ↔ ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] K),
      Function.Surjective f ∧ HasFFR R n (LinearMap.ker f) := Iff.rfl

lemma HasFFR.congr : ∀ (n : ℕ) {K K' : Type u} [AddCommGroup K] [Module R K]
    [AddCommGroup K'] [Module R K'] (_e : K ≃ₗ[R] K'), HasFFR R n K → HasFFR R n K'
  | 0, K, K', _, _, _, _, e, h => by
    rw [hasFFR_zero_iff] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  | n + 1, K, K', _, _, _, _, e, h => by
    rw [hasFFR_succ_iff] at h ⊢
    obtain ⟨k, f, hf, hK⟩ := h
    refine ⟨k, e.toLinearMap ∘ₗ f, e.surjective.comp hf, ?_⟩
    have hker : LinearMap.ker (e.toLinearMap ∘ₗ f) = LinearMap.ker f := LinearEquiv.ker_comp e f
    exact HasFFR.congr n (LinearEquiv.ofEq _ _ hker.symm) hK

section depth

variable [IsLocalRing R]

lemma length_le_depth {M : Type*} [AddCommGroup M] [Module R M] {rs : List R}
    (h1 : IsWeaklyRegular M rs) (h2 : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (rs.length : ℕ∞) ≤ Module.depth R M :=
  le_sSup ⟨rs, h1, h2, rfl⟩

lemma exists_isWeaklyRegular_of_le_depth {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ)
    (h : (n : ℕ∞) ≤ Module.depth R M) :
    ∃ rs : List R, IsWeaklyRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ n ≤ rs.length := by
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (hcon [] (IsWeaklyRegular.nil R M) (by simp)) (by simp)
  · have : Module.depth R M ≤ ((n - 1 : ℕ) : ℕ∞) := by
      apply sSup_le
      rintro _ ⟨rs, h1, h2, rfl⟩
      have := hcon rs h1 h2
      exact_mod_cast (by omega : rs.length ≤ n - 1)
    have h' : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := h.trans this
    have : n ≤ n - 1 := by exact_mod_cast h'
    omega

lemma depth_eq_top_of_subsingleton (M : Type*) [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.depth R M = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  have h1 : IsWeaklyRegular M (List.replicate n (0 : R)) := by
    rw [isWeaklyRegular_iff]
    intro i _ a b _
    exact Subsingleton.elim a b
  have h2 : ∀ r ∈ List.replicate n (0 : R), r ∈ maximalIdeal R := by
    intro r hr
    rw [List.eq_of_mem_replicate hr]
    exact zero_mem _
  simpa using length_le_depth h1 h2

lemma le_depth_pi [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R = d) (k : ℕ) :
    (d : ℕ∞) ≤ Module.depth R (Fin k → R) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [depth_eq_top_of_subsingleton]; exact le_top
  · haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    haveI : Nontrivial (Fin k → R) := Function.nontrivial
    have hR : Module.depth R R = d := by
      have := IsRegularLocalRing.depth_self_eq_ringKrullDim R
      rw [hd] at this
      exact_mod_cast this
    obtain ⟨rs, h1, h2, h3⟩ := exists_isWeaklyRegular_of_le_depth (R := R) (M := R) d hR.ge
    have h1' : IsWeaklyRegular (Fin k → R) rs := (isWeaklyRegular_of_free).mpr h1
    exact le_trans (by exact_mod_cast h3) (length_le_depth h1' h2)

end depth

section syzygy

variable [IsRegularLocalRing R]

theorem hasFFR_of_le_depth (d : ℕ) (hd : ringKrullDim R = d) :
    ∀ n : ℕ, n ≤ d → ∀ (K : Type u) [AddCommGroup K] [Module R K] [Module.Finite R K],
      ((d - n : ℕ) : ℕ∞) ≤ Module.depth R K → HasFFR R n K := by
  intro n
  induction n with
  | zero =>
    intro _ K _ _ _ hK
    rw [hasFFR_zero_iff]
    refine ⟨inferInstance, ?_⟩
    rcases subsingleton_or_nontrivial K with hs | hs
    · exact Module.Free.of_subsingleton R K
    · apply Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing R K
      have h1 : (.some (Module.depth R K) : WithBot ℕ∞) ≤ ringKrullDim R := Module.depth_le_ringKrullDim
      rw [hd] at h1 ⊢
      have h1' : Module.depth R K ≤ d := by exact_mod_cast h1
      have h2 : (d : ℕ∞) ≤ Module.depth R K := by simpa using hK
      have : Module.depth R K = d := le_antisymm h1' h2
      rw [this]; rfl
  | succ n ih =>
    intro hn K _ _ _ hK
    rw [hasFFR_succ_iff]
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R K
    refine ⟨k, f, hf, ih (by omega) _ ?_⟩
    have hDL := P2mAB.DepthLemma.min_depth_depth_add_one_le_depth_of_exact (LinearMap.ker f).subtype f
      (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map f) hf
    refine le_trans (le_min ?_ ?_) hDL
    · exact le_trans (by exact_mod_cast (Nat.sub_le d n)) (le_depth_pi d hd k)
    · have : ((d - n : ℕ) : ℕ∞) = ((d - (n + 1) : ℕ) : ℕ∞) + 1 := by
        norm_cast; omega
      rw [this]
      exact add_le_add hK le_rfl

theorem hasFFR (d : ℕ) (hd : ringKrullDim R = d) (K : Type u) [AddCommGroup K] [Module R K]
    [Module.Finite R K] : HasFFR R d K :=
  hasFFR_of_le_depth d hd d le_rfl K (by simp)

end syzygy

section stablyFree

variable (S : Type v) [CommRing S] [Algebra R S]

noncomputable def kerBaseChangeEquiv [Module.Flat R S] {K : Type w} [AddCommGroup K] [Module R K]
    {k : ℕ} (f : (Fin k → R) →ₗ[R] K) :
    S ⊗[R] (LinearMap.ker f) ≃ₗ[S] LinearMap.ker (f.baseChange S) := by
  let φ : S ⊗[R] (LinearMap.ker f) →ₗ[S] S ⊗[R] (Fin k → R) := (LinearMap.ker f).subtype.baseChange S
  have hφ : ∀ x, φ x ∈ LinearMap.ker (f.baseChange S) := by
    intro x
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (LinearMap.ker (f.baseChange S)) φ hφ) ⟨?_, ?_⟩
  · intro a b hab
    have hab' : φ a = φ b := by simpa using congrArg Subtype.val hab
    have hinj : Function.Injective ((LinearMap.ker f).subtype.lTensor S) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
    apply hinj
    simpa [φ, LinearMap.baseChange_eq_ltensor] using hab'
  · rintro ⟨y, hy⟩
    have hex := Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f)
    have hy' : y ∈ LinearMap.ker (f.lTensor S) := by
      rw [LinearMap.mem_ker] at hy ⊢
      rwa [← LinearMap.baseChange_eq_ltensor]
    obtain ⟨x, hx⟩ := (hex y).mp hy'
    refine ⟨x, Subtype.ext ?_⟩
    simp only [LinearMap.codRestrict_apply]
    rw [← hx, ← LinearMap.baseChange_eq_ltensor]

variable {S} in

lemma step [Module.Flat R S] {K : Type w} [AddCommGroup K] [Module R K] {k : ℕ}
    (f : (Fin k → R) →ₗ[R] K) (hf : Function.Surjective f)
    [Module.Projective S (S ⊗[R] K)] :
    Module.Projective S (S ⊗[R] (LinearMap.ker f)) ∧
      (Module.IsStablyFree S (S ⊗[R] (LinearMap.ker f)) → Module.IsStablyFree S (S ⊗[R] K)) := by

  let e := kerBaseChangeEquiv S f
  let ι : S ⊗[R] (LinearMap.ker f) →ₗ[S] S ⊗[R] (Fin k → R) :=
    (LinearMap.ker (f.baseChange S)).subtype ∘ₗ e.toLinearMap
  let π : S ⊗[R] (Fin k → R) →ₗ[S] S ⊗[R] K := f.baseChange S
  have hι : Function.Injective ι := (Submodule.injective_subtype _).comp e.injective
  have hπ : Function.Surjective π := by
    simpa [π, LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective S hf
  have hιπ : Function.Exact ι π := by
    have h0 : Function.Exact (LinearMap.ker π).subtype π := LinearMap.exact_subtype_ker_map π
    intro y
    rw [h0 y]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm z, by simp [ι]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩

  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  obtain ⟨E, hE1, hE2⟩ := (hιπ.splitSurjectiveEquiv hι) ⟨σ, hσ⟩

  haveI : Module.Free S (S ⊗[R] (Fin k → R)) := inferInstance
  have hproj : Module.Projective S (S ⊗[R] (LinearMap.ker f)) := by
    refine Module.Projective.of_split (E.symm.toLinearMap ∘ₗ LinearMap.inl S _ _)
      (LinearMap.fst S _ _ ∘ₗ E.toLinearMap) ?_
    ext x
    simp
  refine ⟨hproj, fun hsf => ?_⟩
  obtain ⟨N, _, _, _, _, hfree⟩ := Module.IsStablyFree.exist_free_prod S (S ⊗[R] (LinearMap.ker f))
  haveI := hfree
  haveI : Module.Finite S (S ⊗[R] (LinearMap.ker f)) :=
    Module.Finite.of_surjective
      (LinearMap.fst S (S ⊗[R] (LinearMap.ker f)) (S ⊗[R] K) ∘ₗ E.toLinearMap)
      (fun x => ⟨E.symm (x, 0), by simp⟩)

  let E' : ((S ⊗[R] K) × ((S ⊗[R] (LinearMap.ker f)) × N)) ≃ₗ[S]
      ((S ⊗[R] (Fin k → R)) × N) :=
    (LinearEquiv.prodAssoc S (S ⊗[R] K) (S ⊗[R] (LinearMap.ker f)) N).symm ≪≫ₗ
      ((LinearEquiv.prodComm S (S ⊗[R] K) (S ⊗[R] (LinearMap.ker f))).prodCongr
        (LinearEquiv.refl S N)) ≪≫ₗ
      (E.symm.prodCongr (LinearEquiv.refl S N))
  haveI : Module.Free S ((S ⊗[R] K) × ((S ⊗[R] (LinearMap.ker f)) × N)) := Module.Free.of_equiv E'.symm
  exact Module.IsStablyFree.of_free_prod S (S ⊗[R] K) ((S ⊗[R] (LinearMap.ker f)) × N)

theorem isStablyFree_of_hasFFR [Module.Flat R S] :
    ∀ (n : ℕ) (K : Type u) [AddCommGroup K] [Module R K] [Module.Projective S (S ⊗[R] K)],
      HasFFR R n K → Module.IsStablyFree S (S ⊗[R] K) := by
  intro n
  induction n with
  | zero =>
    intro K _ _ _ hK
    rw [hasFFR_zero_iff] at hK
    obtain ⟨_, _⟩ := hK
    infer_instance
  | succ n ih =>
    intro K _ _ _ hK
    rw [hasFFR_succ_iff] at hK
    obtain ⟨k, f, hf, hK'⟩ := hK
    obtain ⟨hproj, hstep⟩ := step (S := S) f hf
    exact hstep (ih _ hK')

end stablyFree

theorem isStablyFree_baseChange (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Module.Flat R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective S (S ⊗[R] M)] :
    Module.IsStablyFree S (S ⊗[R] M) := by

  set d : ℕ := (maximalIdeal R).spanFinrank with hd
  have hdim : ringKrullDim R = d := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm

  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨hproj, hstep⟩ := step (S := S) f hf
  haveI := hproj
  refine hstep (isStablyFree_of_hasFFR S d _ ?_)

  exact hasFFR d hdim _

end P2mAB.StablyFree

namespace P2mAB

section idealLoc

variable {A : Type*} [CommRing A] (M : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
  [IsLocalization M B]

noncomputable def tensorIdealEquivMap (I : Ideal A) :
    B ⊗[A] I ≃ₗ[B] (I.map (algebraMap A B) : Ideal B) :=
  have hbc : IsBaseChange B (I.toLocalized' B M (Algebra.linearMap A B)) :=
    IsLocalizedModule.isBaseChange M B _
  hbc.equiv ≪≫ₗ LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map B M I)

end idealLoc

section principal

variable {S : Type*} [CommRing S]

noncomputable def linearEquivOfSpanSingleton [IsDomain S] {π : S} (hπ : π ≠ 0) :
    (Ideal.span {π} : Ideal S) ≃ₗ[S] S :=
  (LinearEquiv.toSpanNonzeroSingleton S S π hπ).symm

lemma isPrincipal_of_linearEquiv (P : Ideal S) (e : P ≃ₗ[S] S) : P.IsPrincipal := by
  refine ⟨⟨(e.symm 1 : S), le_antisymm ?_ ?_⟩⟩
  · intro p hp
    have : (⟨p, hp⟩ : P) = e ⟨p, hp⟩ • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    have h2 : p = e ⟨p, hp⟩ * (e.symm 1 : S) := by
      simpa using congrArg Subtype.val this
    rw [h2]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le (α := S) (I := P) (s := {(e.symm 1 : S)}), Set.singleton_subset_iff]
    exact (e.symm 1).2

end principal

theorem ufd_of_heightOne_principal (S : Type*) [CommRing S] [IsDomain S] [IsNoetherianRing S]
    (h : ∀ P : Ideal S, P.IsPrime → P ≠ ⊥ → P.height ≤ 1 → P.IsPrincipal) :
    UniqueFactorizationMonoid S := by
  refine (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime).mpr fun I hI hIp => ?_
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨P, hPmin, hPI⟩ := Ideal.exists_minimalPrimes_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haI) : Ideal.span {a} ≤ I)
  haveI hPp : P.IsPrime := hPmin.1.1
  have haP : a ∈ P := hPmin.1.2 (Ideal.subset_span rfl)
  have hP0 : P ≠ ⊥ := fun h0 => ha0 (by simpa [h0] using haP)
  have hPh : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin
  obtain ⟨π, hπ⟩ := (h P hPp hP0 hPh).principal
  have hπP : P = Ideal.span {π} := hπ
  have hπ0 : π ≠ 0 := by rintro rfl; exact hP0 (by simp [hπP])
  refine ⟨π, hPI (hπP ▸ Ideal.subset_span rfl), ?_⟩
  exact (Ideal.span_singleton_prime hπ0).mp (hπP ▸ hPp)

section locallyPrincipal

variable {S : Type u} [CommRing S] [IsDomain S] (P : Ideal S) (hP0 : P ≠ ⊥)
  (hloc : ∀ (Q : Ideal S) [Q.IsPrime], (P.map (algebraMap S (Localization.AtPrime Q))).IsPrincipal)

include hP0 hloc

lemma nonempty_linearEquiv_localization (Q : Ideal S) [Q.IsPrime] :
    Nonempty ((P.map (algebraMap S (Localization.AtPrime Q)) : Ideal (Localization.AtPrime Q))
      ≃ₗ[Localization.AtPrime Q] Localization.AtPrime Q) := by
  obtain ⟨π, hπ⟩ := (hloc Q).principal
  have hinj : Function.Injective (algebraMap S (Localization.AtPrime Q)) :=
    IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors
  have hπ0 : π ≠ 0 := by
    rintro rfl
    obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have : algebraMap S (Localization.AtPrime Q) a ∈ P.map (algebraMap S _) := Ideal.mem_map_of_mem _ haP
    rw [hπ, Submodule.span_singleton_eq_bot.mpr rfl] at this
    exact ha0 (hinj (by simpa using this))
  rw [show P.map (algebraMap S (Localization.AtPrime Q)) = Ideal.span {π} from hπ]
  exact ⟨linearEquivOfSpanSingleton hπ0⟩

lemma projective [IsNoetherianRing S] : Module.Projective S P := by
  haveI : Module.FinitePresentation S P := Module.finitePresentation_of_finite S P
  refine Module.projective_of_localization_maximal fun Q hQ => ?_
  haveI := hQ
  obtain ⟨e⟩ := nonempty_linearEquiv_localization P hP0 hloc Q
  let Sq := Localization.AtPrime Q
  have eL : Sq ⊗[S] P ≃ₗ[Sq] LocalizedModule Q.primeCompl P :=
    (IsLocalizedModule.isBaseChange Q.primeCompl Sq (LocalizedModule.mkLinearMap Q.primeCompl P)).equiv
  exact Module.Projective.of_equiv (eL.symm ≪≫ₗ tensorIdealEquivMap Q.primeCompl Sq P ≪≫ₗ e).symm

lemma invertible [IsNoetherianRing S] : Module.Invertible S P := by
  haveI := projective P hP0 hloc
  refine Module.Invertible.of_projective_of_forall_finrank_eq_one P fun K _ _ => ?_

  let q : Ideal S := RingHom.ker (algebraMap S K)
  haveI : q.IsPrime := RingHom.ker_isPrime _
  let Sq := Localization.AtPrime q
  have hunit : ∀ y : q.primeCompl, IsUnit (algebraMap S K y) := by
    intro y
    have : algebraMap S K y ≠ 0 := fun h => y.2 (by simpa [q, RingHom.mem_ker] using h)
    exact isUnit_iff_ne_zero.mpr this
  letI : Algebra Sq K := (IsLocalization.lift (M := q.primeCompl) hunit).toAlgebra
  haveI : IsScalarTower S Sq K := IsScalarTower.of_algebraMap_eq fun s => by
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq]
  obtain ⟨e⟩ := nonempty_linearEquiv_localization P hP0 hloc q
  let e₁ : Sq ⊗[S] P ≃ₗ[Sq] Sq := tensorIdealEquivMap q.primeCompl Sq P ≪≫ₗ e
  let e₂ : K ⊗[S] P ≃ₗ[K] K :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S Sq K K P).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e₁ ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid Sq K K
  rw [e₂.finrank_eq, Module.finrank_self]

lemma isPrincipal_of_isStablyFree [IsNoetherianRing S] [Module.IsStablyFree S P] : P.IsPrincipal := by
  haveI := invertible P hP0 hloc
  haveI := Module.free_of_isStablyFree_of_invertible S P
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := S) (M := P)).mp inferInstance
  exact isPrincipal_of_linearEquiv P e

end locallyPrincipal

section regular

variable {R : Type u} [CommRing R]

lemma isRegularRing_localization [IsRegularRing R] (M : Submonoid R) :
    IsRegularRing (Localization M) := by
  haveI : IsNoetherianRing (Localization M) := IsLocalization.isNoetherianRing M _ inferInstance
  refine (isRegularRing_iff).mpr fun p hp => ?_
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p).toRingEquiv

end regular

section induction

lemma exists_prime_mem_maximalIdeal (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (h : maximalIdeal R ≠ ⊥) : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ Prime x := by

  have hlt : maximalIdeal R ^ 2 < maximalIdeal R := by
    refine lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) fun heq => h ?_
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (IsNoetherian.noetherian _) (le_of_eq ?_) (IsLocalRing.maximalIdeal_le_jacobson _)
    rw [Ideal.smul_eq_mul, ← pow_two, heq]
  obtain ⟨x, hxm, hx2⟩ := SetLike.exists_of_lt hlt
  refine ⟨x, hxm, hx2, ?_⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)

  have hxu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hxm
  haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by simpa [Ideal.span_singleton_eq_top] using hxu)
  haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmin : ∀ p ∈ minimalPrimes R, x ∉ p := by
    intro p hp
    rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hp
    subst hp
    simpa using hx0
  have hreg := (IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    R hxm hx2 hmin).1
  haveI := IsRegularLocalRing.isDomain (R ⧸ Ideal.span {x})
  have : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  exact (Ideal.span_singleton_prime hx0).mp this

theorem ufd_of_ringKrullDim_le (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsRegularRing R],
      ringKrullDim R ≤ d → UniqueFactorizationMonoid R := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro R _ _ _ _ hd
  haveI : IsRegularLocalRing R := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  by_cases hm : maximalIdeal R = ⊥
  ·
    refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun I hI hIp => ?_
    exact absurd (le_bot_iff.mp (hm ▸ IsLocalRing.le_maximalIdeal hIp.ne_top)) hI
  obtain ⟨x, hxm, -, hx⟩ := exists_prime_mem_maximalIdeal R hm
  have hx0 : x ≠ 0 := hx.ne_zero

  let S := Localization.Away x
  haveI : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers x) S inferInstance
  haveI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers x)
  suffices UniqueFactorizationMonoid S from
    UniqueFactorizationMonoid.of_isLocalization_away_of_prime hx S

  have hdimR : ((maximalIdeal R).height : WithBot ℕ∞) ≤ d := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact hd
  have hdimR' : (maximalIdeal R).height ≤ d := by exact_mod_cast hdimR

  have hSQ : ∀ (Q : Ideal S) [Q.IsPrime], UniqueFactorizationMonoid (Localization.AtPrime Q) := by
    intro Q hQ
    let q : Ideal R := Q.comap (algebraMap R S)
    haveI hq : q.IsPrime := Ideal.comap_isPrime _ Q
    have hxq : x ∉ q := fun hxq =>
      hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hxq (IsLocalization.Away.algebraMap_isUnit x))
    have hqm : q < maximalIdeal R :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hq.ne_top) fun h => hxq (h ▸ hxm)
    have hlt : q.height < (maximalIdeal R).height :=
      Ideal.height_strict_mono_of_isPrime_of_isPrime hqm
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := q))
    have hnd : n < d := by
      have : (n : ℕ∞) < d := by rw [hn]; exact lt_of_lt_of_le hlt hdimR'
      exact_mod_cast this
    haveI : IsRegularRing (Localization.AtPrime q) := isRegularRing_localization q.primeCompl
    have hdimq : ringKrullDim (Localization.AtPrime q) ≤ n := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), ← hn]
      rfl
    have hufd := ih n hnd (Localization.AtPrime q) hdimq
    exact MulEquiv.uniqueFactorizationMonoid
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers x) Q).toMulEquiv
      hufd

  refine ufd_of_heightOne_principal S fun P hPp hP0 hPh => ?_

  have hloc : ∀ (Q : Ideal S) [Q.IsPrime],
      (P.map (algebraMap S (Localization.AtPrime Q))).IsPrincipal := by
    intro Q hQ
    by_cases hPQ : P ≤ Q
    · haveI := hSQ Q
      have hdisj : Disjoint (Q.primeCompl : Set S) (P : Set S) := by
        rw [Set.disjoint_left]
        intro s hs hsP
        exact hs (hPQ hsP)
      haveI hP' : (P.map (algebraMap S (Localization.AtPrime Q))).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hPp hdisj
      have hinj : Function.Injective (algebraMap S (Localization.AtPrime Q)) :=
        IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors
      have hP'0 : P.map (algebraMap S (Localization.AtPrime Q)) ≠ ⊥ := by
        obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
        intro h0
        have : algebraMap S (Localization.AtPrime Q) a ∈ P.map (algebraMap S _) :=
          Ideal.mem_map_of_mem _ haP
        rw [h0, Ideal.mem_bot] at this
        exact ha0 (hinj (by simpa using this))
      obtain ⟨π, hπP, hπ⟩ := hP'.exists_mem_prime_of_ne_bot hP'0
      have hle : Ideal.span {π} ≤ P.map (algebraMap S (Localization.AtPrime Q)) :=
        (Ideal.span_singleton_le_iff_mem _).mpr hπP
      haveI : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
      have hh : (P.map (algebraMap S (Localization.AtPrime Q))).height ≤ (Ideal.span {π}).height := by
        rw [IsLocalization.height_map_of_disjoint Q.primeCompl P hdisj]
        refine hPh.trans ?_
        exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
      have heq := Ideal.eq_of_le_of_height_le (I := Ideal.span {π}) hle hh
      exact ⟨⟨π, heq.symm⟩⟩
    · obtain ⟨s, hsP, hsQ⟩ := Set.not_subset.mp hPQ
      have htop : P.map (algebraMap S (Localization.AtPrime Q)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsP)
          (IsLocalization.map_units (M := Q.primeCompl) _ ⟨s, hsQ⟩)
      rw [htop]
      exact ⟨⟨1, by simp⟩⟩

  let 𝔭 : Ideal R := P.comap (algebraMap R S)
  have hmap : 𝔭.map (algebraMap R S) = P := IsLocalization.map_under (Submonoid.powers x) S P
  haveI := projective P hP0 hloc
  let eP : S ⊗[R] 𝔭 ≃ₗ[S] P :=
    tensorIdealEquivMap (Submonoid.powers x) S 𝔭 ≪≫ₗ LinearEquiv.ofEq _ _ (by rw [hmap])
  haveI : Module.Projective S (S ⊗[R] 𝔭) := Module.Projective.of_equiv eP.symm
  haveI : Module.IsStablyFree S (S ⊗[R] 𝔭) :=
    P2mAB.StablyFree.isStablyFree_baseChange R S 𝔭
  haveI : Module.IsStablyFree S P := Module.IsStablyFree.equiv eP
  exact isPrincipal_of_isStablyFree P hP0 hloc

end induction

end P2mAB

open P2mAB IsLocalRing in

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsRegularRing R] :
    UniqueFactorizationMonoid R := by
  haveI : IsRegularLocalRing R := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  refine ufd_of_ringKrullDim_le (maximalIdeal R).spanFinrank R (le_of_eq ?_)
  exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm

end S_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing
end P2MW
export P2MW.S_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing (solution)
