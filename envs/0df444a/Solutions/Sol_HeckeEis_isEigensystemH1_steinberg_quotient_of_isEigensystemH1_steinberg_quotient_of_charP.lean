-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3f403891-2d57-57a3-b5f9-c309ae4923bf

import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_ModularCurve_HeckeAlgebraHom
import Theorems.Thm_CuspidalType_exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod
import Theorems.Thm_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun
import Theorems.Thm_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
import Theorems.Thm_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange
import Theorems.Thm_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP

set_option autoImplicit false
open CongruenceSubgroup Polynomial

open Matrix

section DescentRehearsalA

private theorem exists_finset_iInf_eq_bot_desc {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {I : Type} (K : I → Submodule F V) (h : ⨅ l, K l = ⊥) :
    ∃ s : Finset I, ⨅ l ∈ s, K l = ⊥ := by
  classical
  have hP : ∃ n : ℕ, ∃ s : Finset I, Module.finrank F ↥(⨅ l ∈ s, K l) = n := ⟨_, ∅, rfl⟩
  obtain ⟨s₀, hs₀⟩ := Nat.find_spec hP
  refine ⟨s₀, ?_⟩
  rw [eq_bot_iff, ← h, le_iInf_iff]
  intro l
  have hle : ⨅ m ∈ insert l s₀, K m ≤ ⨅ m ∈ s₀, K m :=
    le_iInf₂ fun m hm => iInf₂_le m (Finset.mem_insert_of_mem hm)
  have hmin : Nat.find hP ≤ Module.finrank F ↥(⨅ m ∈ insert l s₀, K m) :=
    Nat.find_min' hP ⟨insert l s₀, rfl⟩
  have hrank : Module.finrank F ↥(⨅ m ∈ insert l s₀, K m) = Module.finrank F ↥(⨅ m ∈ s₀, K m) :=
    le_antisymm (Submodule.finrank_mono hle) (hs₀ ▸ hmin)
  have heq : ⨅ m ∈ insert l s₀, K m = ⨅ m ∈ s₀, K m := Submodule.eq_of_le_of_finrank_eq hle hrank
  calc ⨅ m ∈ s₀, K m = ⨅ m ∈ insert l s₀, K m := heq.symm
    _ ≤ K l := iInf₂_le l (Finset.mem_insert_self l s₀)

private theorem exists_common_eigenvector_of_map_desc {F L : Type} [Field F] [Field L] (i : F →+* L) {I : Type} {t : ℕ}
    (A : I → Matrix (Fin t) (Fin t) F) (lam : I → F) (r : Fin t → L) (hr : r ≠ 0)
    (h : ∀ l : I, (A l).map i *ᵥ r = i (lam l) • r) :
    ∃ r' : Fin t → F, r' ≠ 0 ∧ ∀ l : I, A l *ᵥ r' = lam l • r' := by
  classical
  by_contra hcon
  set K : I → Submodule F (Fin t → F) :=
    fun l => LinearMap.ker (Matrix.toLin' (A l - lam l • (1 : Matrix (Fin t) (Fin t) F))) with hK
  have hmemK : ∀ (l : I) (v : Fin t → F), v ∈ K l ↔ A l *ᵥ v = lam l • v := by
    intro l v
    simp only [hK, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
  have hbot : ⨅ l, K l = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    by_contra hv0
    exact hcon ⟨v, hv0, fun l => (hmemK l v).1 ((Submodule.mem_iInf K).1 hv l)⟩
  obtain ⟨s, hs⟩ := exists_finset_iInf_eq_bot_desc K hbot
  let M : Matrix (↥s × Fin t) (Fin t) F :=
    Matrix.of fun p j => (A p.1 - lam p.1 • (1 : Matrix (Fin t) (Fin t) F)) p.2 j
  have hM : ∀ (v : Fin t → F) (p : ↥s × Fin t),
      (M *ᵥ v) p = ((A p.1 - lam p.1 • (1 : Matrix (Fin t) (Fin t) F)) *ᵥ v) p.2 :=
    fun _ _ => rfl
  have hMker : LinearMap.ker (Matrix.toLin' M) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
    have hv' : v ∈ ⨅ l ∈ s, K l := by
      refine (Submodule.mem_iInf _).2 fun l => (Submodule.mem_iInf _).2 fun hl => (hmemK l v).2 ?_
      have h0 : (A l - lam l • (1 : Matrix (Fin t) (Fin t) F)) *ᵥ v = 0 := by
        funext k
        have hk := congrFun hv (⟨l, hl⟩, k)
        rw [hM] at hk
        exact hk
      rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    rw [hs] at hv'
    exact hv'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' M) hMker
  have hBM : LinearMap.toMatrix' g * M = 1 := by
    have h1 := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1
  have hMmap : M.map i =
      Matrix.of fun (p : ↥s × Fin t) j => ((A p.1).map i - i (lam p.1) • (1 : Matrix (Fin t) (Fin t) L)) p.2 j := by
    ext p j
    simp only [M, Matrix.map_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, map_sub, map_mul, apply_ite i, map_one, map_zero]
  have hMr : M.map i *ᵥ r = 0 := by
    funext p
    rw [hMmap]
    change (((A p.1).map i - i (lam p.1) • (1 : Matrix (Fin t) (Fin t) L)) *ᵥ r) p.2 = 0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h p.1, sub_self, Pi.zero_apply]
  have hr0 : r = 0 := by
    have h2 := congrArg (fun w => (LinearMap.toMatrix' g).map i *ᵥ w) hMr
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rwa [← Matrix.map_mul, hBM, Matrix.map_one (i : F → L) (map_zero i) (map_one i), Matrix.one_mulVec] at h2
  exact hr hr0

end DescentRehearsalA

section DescentRehearsalB1

private theorem exists_addMonoidHom_retraction_desc {R K : Type} [Field R] [Field K] [Algebra R K]
    {Λ V : Type} [AddCommGroup Λ] [Module R Λ] [AddCommGroup V] [Module K V]
    (ι : Λ →+ V) (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    {d : ℕ} (bΛ : Module.Basis (Fin d) R Λ) (bV : Module.Basis (Fin d) K V) (hb : ∀ j : Fin d, bV j = ι (bΛ j))
    {G : Type} [Monoid G] (ρR : Representation R G Λ) (ρ : Representation K G V)
    (hιρ : ∀ (g : G) (x : Λ), ι (ρR g x) = ρ g (ι x)) :
    ∃ S : V →+ Λ, (∀ x : Λ, S (ι x) = x) ∧ ∀ (g : G) (v : V), S (ρ g v) = ρR g (S v) := by
  classical

  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap R K)
    (LinearMap.ker_eq_bot.2 (algebraMap R K).injective)
  have hs' : ∀ r : R, s (algebraMap R K r) = r := fun r => LinearMap.congr_fun hs r
  have hsmul : ∀ (c : K) (r : R), s (c * algebraMap R K r) = s c * r := by
    intro c r
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

  let S : V →+ Λ :=
    { toFun := fun v => ∑ j : Fin d, s (bV.repr v j) • bΛ j
      map_zero' := by simp
      map_add' := by
        intro v w
        simp only [map_add, Finsupp.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  have hS : ∀ c : Fin d → K, S (∑ j : Fin d, c j • bV j) = ∑ j : Fin d, s (c j) • bΛ j := by
    intro c
    show ∑ j : Fin d, s (bV.repr (∑ j : Fin d, c j • bV j) j) • bΛ j = _
    simp only [Module.Basis.repr_sum_self]
  have hι : ∀ x : Fin d → R, ι (∑ j : Fin d, x j • bΛ j) = ∑ j : Fin d, algebraMap R K (x j) • bV j := by
    intro x
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hιs, hb]
  refine ⟨S, ?_, ?_⟩
  · intro x
    conv_lhs => rw [← bΛ.sum_repr x, hι, hS]
    simp only [hs']
    exact bΛ.sum_repr x
  · intro g v

    set m : Fin d → Fin d → R := fun j k => bΛ.repr (ρR g (bΛ j)) k with hm
    have hρR : ∀ j : Fin d, ρR g (bΛ j) = ∑ k : Fin d, m j k • bΛ k := fun j => (bΛ.sum_repr _).symm
    have hρ : ∀ j : Fin d, ρ g (bV j) = ∑ k : Fin d, algebraMap R K (m j k) • bV k := by
      intro j
      rw [hb, ← hιρ, hρR, hι]
    set c : Fin d → K := fun j => bV.repr v j with hc
    have hv : v = ∑ j : Fin d, c j • bV j := (bV.sum_repr v).symm
    have hleft : ρ g v = ∑ k : Fin d, (∑ j : Fin d, c j * algebraMap R K (m j k)) • bV k := by
      rw [hv, map_sum]
      simp only [map_smul, hρ, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    rw [hleft, hS, hv, hS, map_sum]
    simp only [map_smul, hρR, Finset.smul_sum, smul_smul, map_sum, hsmul, Finset.sum_smul]
    rw [Finset.sum_comm]

end DescentRehearsalB1

section DescentRehearsalEF

private theorem mulVec_repr_desc {K : Type} [Field K] {H : Type} [AddCommGroup H] [Module K H] {t : ℕ}
    (c : Module.Basis (Fin t) K H) (T : H →ₗ[K] H) {R : Type} [CommRing R] (f : R →+* K)
    (A : Matrix (Fin t) (Fin t) R) (hA : ∀ j : Fin t, T (c j) = ∑ i : Fin t, f (A i j) • c i) (x : H) (μ : K)
    (hx : T x = μ • x) : A.map f *ᵥ (fun i => c.repr x i) = μ • fun i => c.repr x i := by
  have hTx : T x = ∑ i : Fin t, (∑ j : Fin t, f (A i j) * c.repr x j) • c i := by
    conv_lhs => rw [← c.sum_repr x]
    rw [map_sum]
    simp only [map_smul, hA, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have hrepr : c.repr (T x) = c.repr (μ • x) := by rw [hx]
  rw [hTx, map_smul] at hrepr
  funext i
  have hi := congrArg (fun φ : Fin t →₀ K => φ i) hrepr
  simp only [Module.Basis.repr_sum_self, Finsupp.smul_apply, smul_eq_mul] at hi
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
  exact hi

private theorem map_sum_smul_eq_desc {K : Type} [Field K] {H : Type} [AddCommGroup H] [Module K H] {t : ℕ}
    (c : Fin t → H) (T : H →ₗ[K] H) {R : Type} [CommRing R] (f : R →+* K) (A : Matrix (Fin t) (Fin t) R)
    (hA : ∀ j : Fin t, T (c j) = ∑ i : Fin t, f (A i j) • c i) (r' : Fin t → R) (μ : R) (hr' : A *ᵥ r' = μ • r') :
    T (∑ i : Fin t, f (r' i) • c i) = f μ • ∑ i : Fin t, f (r' i) • c i := by
  have hcoord : ∀ k : Fin t, ∑ i : Fin t, f (r' i) * f (A k i) = f μ * f (r' k) := by
    intro k
    have hk := congrFun hr' k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hk
    rw [← map_mul, ← hk, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
  rw [map_sum]
  simp only [map_smul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, hcoord k]

end DescentRehearsalEF

section DescentCore

open CongruenceSubgroup

private noncomputable def heckeOnCocycles_dc (N ℓ : ℕ) [NeZero ℓ] {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a) :
    ↥(HeckeEis.coeffCocycles ρ) →ₗ[K] ↥(HeckeEis.coeffCocycles ρ) where
  toFun z := ⟨HeckeEis.coeffHeckeFun N ℓ ρ a z, HeckeEis.coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha z.2⟩
  map_add' z w := by
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_add, HeckeEis.coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_smul, HeckeEis.coeffHeckeFun_apply, Pi.smul_apply, map_smul, Finset.smul_sum,
      RingHom.id_apply]

private theorem heckeOnCocycles_dc_coe (N ℓ : ℕ) [NeZero ℓ] {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a) (z : ↥(HeckeEis.coeffCocycles ρ)) :
    ((heckeOnCocycles_dc N ℓ ρ a ha z : ↥(HeckeEis.coeffCocycles ρ)) : Gamma0 N → V) =
      HeckeEis.coeffHeckeFun N ℓ ρ a z :=
  rfl

private theorem exists_isCoeffHeckeOnH1_dc (N ℓ : ℕ) [NeZero ℓ] {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a) :
    ∃ T : HeckeEis.coeffH1 ρ →ₗ[K] HeckeEis.coeffH1 ρ, HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ a T := by
  have hB : (HeckeEis.coeffCoboundaries ρ).comap (HeckeEis.coeffCocycles ρ).subtype ≤
      ((HeckeEis.coeffCoboundaries ρ).comap (HeckeEis.coeffCocycles ρ).subtype).comap
        (heckeOnCocycles_dc N ℓ ρ a ha) := by
    intro z hz
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hz
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply, heckeOnCocycles_dc_coe]
    exact HeckeEis.coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz
  exact ⟨Submodule.mapQ _ _ (heckeOnCocycles_dc N ℓ ρ a ha) hB, fun z => ⟨heckeOnCocycles_dc N ℓ ρ a ha z, rfl, rfl⟩⟩

private theorem injective_of_retraction_dc {N : ℕ} {R K : Type} [Field R] [Field K] [Algebra R K]
    {Λ V : Type} [AddCommGroup Λ] [Module R Λ] [AddCommGroup V] [Module K V]
    (ρR : Representation R (Gamma0 N) Λ) (ρ : Representation K (Gamma0 N) V) (ι : Λ →+ V) (S : V →+ Λ)
    (hSι : ∀ x : Λ, S (ι x) = x) (hSρ : ∀ (g : Gamma0 N) (v : V), S (ρ g v) = ρR g (S v))
    (Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ)
    (hΦ : ∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ),
      (∀ g : Gamma0 N, (w : Gamma0 N → V) g = ι ((z : Gamma0 N → Λ) g)) ∧
        Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ w) :
    Function.Injective Φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1Mk_surjective ρR x
  obtain ⟨w, hw, hΦz⟩ := hΦ z
  rw [hΦz, HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff] at hx
  obtain ⟨v, hv⟩ := hx
  rw [HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff]
  refine ⟨S v, funext fun g => ?_⟩
  have h1 : (z : Gamma0 N → Λ) g = S ((w : Gamma0 N → V) g) := by rw [hw, hSι]
  have h2 : (w : Gamma0 N → V) g = ρ g v - v := by rw [← hv]
  rw [h1, h2, map_sub, hSρ]

end DescentCore

section DescentAssembly

open CongruenceSubgroup

private theorem isEigensystemH1_descent_dc (N : ℕ) [Group.FG (Gamma0 N)] {F K₀ : Type} [Field F] [Field K₀]
    [Algebra F K₀] {Λ V₀ : Type} [AddCommGroup Λ] [Module F Λ] [AddCommGroup V₀] [Module K₀ V₀]
    (ρF : Representation F (Gamma0 N) Λ) (ρ₀ : Representation K₀ (Gamma0 N) V₀)
    (ι : Λ →ₛₗ[algebraMap F K₀] V₀) (hιρ : ∀ (g : Gamma0 N) (x : Λ), ι (ρF g x) = ρ₀ g (ι x))
    {d : ℕ} (bΛ : Module.Basis (Fin d) F Λ) (bV : Module.Basis (Fin d) K₀ V₀) (hb : ∀ i : Fin d, bV i = ι (bΛ i))
    (aF : ℕ → (Λ →ₗ[F] Λ)) (a₀ : ℕ → (V₀ →ₗ[K₀] V₀)) (hιa : ∀ (ℓ : ℕ) (x : Λ), ι (aF ℓ x) = a₀ ℓ (ι x))
    (S₀ : Set ℕ)
    (haF : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      aF ℓ ∘ₗ ρF (HeckeEis.heckeConj N ℓ u) = ρF (u : Gamma0 N) ∘ₗ aF ℓ)
    (lam : ℕ → F) (h₀ : HeckeEis.IsEigensystemH1 N ρ₀ a₀ S₀ (fun ℓ => algebraMap F K₀ (lam ℓ))) :
    HeckeEis.IsEigensystemH1 N ρF aF S₀ lam := by
  classical
  have hιs : ∀ (r : F) (x : Λ), ι.toAddMonoidHom (r • x) = algebraMap F K₀ r • ι.toAddMonoidHom x :=
    fun r x => ι.map_smulₛₗ r x
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, -⟩ := HeckeEis.exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom N
    (algebraMap F K₀) ρF ρ₀ ι.toAddMonoidHom hιs hιρ aF a₀ hιa
  obtain ⟨S, hSι, hSρ⟩ := exists_addMonoidHom_retraction_desc ι.toAddMonoidHom hιs bΛ bV hb ρF ρ₀ hιρ
  have hΦinj : Function.Injective Φ := injective_of_retraction_dc ρF ρ₀ ι.toAddMonoidHom S hSι hSρ Φ hΦ1
  unfold HeckeEis.IsEigensystemH1 at h₀ ⊢
  obtain ⟨x₀, hx₀, hT₀⟩ := h₀
  let I : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀}
  have hNZ : ∀ l : I, NeZero l.1 := fun l => ⟨l.2.1.ne_zero⟩
  have hT₀' : ∀ l : I, ∃ T : HeckeEis.coeffH1 ρ₀ →ₗ[K₀] HeckeEis.coeffH1 ρ₀,
      (haveI := hNZ l; HeckeEis.IsCoeffHeckeOnH1 N l.1 ρ₀ (a₀ l.1) T) ∧ T x₀ = algebraMap F K₀ (lam l.1) • x₀ :=
    fun l => hT₀ l.1 l.2.1 l.2.2.1 l.2.2.2
  choose T₀ hT₀hecke hT₀eig using hT₀'
  have hTF' : ∀ l : I, ∃ T : HeckeEis.coeffH1 ρF →ₗ[F] HeckeEis.coeffH1 ρF,
      (haveI := hNZ l; HeckeEis.IsCoeffHeckeOnH1 N l.1 ρF (aF l.1) T) := fun l =>
    haveI := hNZ l
    exists_isCoeffHeckeOnH1_dc N l.1 ρF (aF l.1) (haF l.1 l.2.1 l.2.2.1 l.2.2.2)
  choose TF hTFhecke using hTF'
  have hcomm : ∀ (l : I) (x : HeckeEis.coeffH1 ρF), Φ (TF l x) = T₀ l (Φ x) := fun l x =>
    haveI := hNZ l
    hΦ3 l.1 (TF l) (T₀ l) (hTFhecke l) (hT₀hecke l) x
  obtain ⟨t, b, c, hc, -, hA⟩ := HeckeEis.exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
    (algebraMap F K₀).injective N ρF ρ₀ ι.toAddMonoidHom hιs hιρ bΛ bV hb Φ hΦ1
    (fun l : I => (TF l).toAddMonoidHom) (fun l : I => (T₀ l).toAddMonoidHom) hcomm
  choose A hA using hA
  have hA' : ∀ (l : I) (j : Fin t), T₀ l (c j) = ∑ i : Fin t, algebraMap F K₀ (A l i j) • c i := fun l j => hA l j
  set r : Fin t → K₀ := fun i => c.repr x₀ i with hr
  have hr0 : r ≠ 0 := by
    intro h
    apply hx₀
    have hx : x₀ = ∑ i : Fin t, c.repr x₀ i • c i := (c.sum_repr x₀).symm
    rw [hx]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : c.repr x₀ i = 0 := congrFun h i
    rw [hi, zero_smul]
  have hmat : ∀ l : I, (A l).map (algebraMap F K₀) *ᵥ r = algebraMap F K₀ (lam l.1) • r :=
    fun l => mulVec_repr_desc c (T₀ l) (algebraMap F K₀) (A l) (hA' l) x₀ _ (hT₀eig l)
  obtain ⟨r', hr'0, hr'⟩ :=
    exists_common_eigenvector_of_map_desc (algebraMap F K₀) A (fun l : I => lam l.1) r hr0 hmat
  have hΦsum : Φ (∑ i : Fin t, r' i • b i) = ∑ i : Fin t, algebraMap F K₀ (r' i) • c i := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hΦ2, hc]
  refine ⟨∑ i : Fin t, r' i • b i, ?_, fun ℓ hℓ hℓN hℓS => ?_⟩
  · intro h0
    apply hr'0
    rw [h0, map_zero] at hΦsum
    funext i
    have hi := congrArg (fun φ : Fin t →₀ K₀ => φ i) (congrArg c.repr hΦsum)
    simp only [map_zero, Finsupp.zero_apply, Module.Basis.repr_sum_self] at hi
    exact (algebraMap F K₀).injective (by rw [Pi.zero_apply, map_zero]; exact hi.symm)
  · let l : I := ⟨ℓ, hℓ, hℓN, hℓS⟩
    refine ⟨TF l, hTFhecke l, ?_⟩
    apply hΦinj
    rw [hcomm, hΦ2, hΦsum, map_sum_smul_eq_desc c (T₀ l) (algebraMap F K₀) (A l) (hA' l) r' (lam ℓ) (hr' l)]

end DescentAssembly

section DescentGlue

open CongruenceSubgroup

private noncomputable def adj_dg (q : ℕ) [Fact q.Prime] {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CuspidalType.GL2 q) V) : ℕ → (V →ₗ[K] V) := fun ℓ =>
  if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id

private theorem adj_dg_of_ne_zero (q : ℕ) [Fact q.Prime] {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K (CuspidalType.GL2 q) V) (ℓ : ℕ) (h : (ℓ : ZMod q) ≠ 0) :
    adj_dg q ρ ℓ = ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) := by
  simp only [adj_dg, dif_pos h]

private theorem adj_dg_of_eq_zero (q : ℕ) [Fact q.Prime] {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K (CuspidalType.GL2 q) V) (ℓ : ℕ) (h : ¬ (ℓ : ZMod q) ≠ 0) :
    adj_dg q ρ ℓ = LinearMap.id := by
  simp only [adj_dg, dif_neg h]

private theorem map_adj_dg (q : ℕ) [Fact q.Prime] {K₁ K₂ : Type} [Field K₁] [Field K₂] (σ : K₁ →+* K₂)
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module K₁ V₁] [AddCommGroup V₂] [Module K₂ V₂]
    (ρ₁ : Representation K₁ (CuspidalType.GL2 q) V₁) (ρ₂ : Representation K₂ (CuspidalType.GL2 q) V₂)
    (j : V₁ →ₛₗ[σ] V₂) (hj : ∀ (g : CuspidalType.GL2 q) (v : V₁), j (ρ₁ g v) = ρ₂ g (j v)) (ℓ : ℕ) (v : V₁) :
    j (adj_dg q ρ₁ ℓ v) = adj_dg q ρ₂ ℓ (j v) := by
  by_cases h : ((ℓ : ZMod q) ≠ 0)
  · rw [adj_dg_of_ne_zero q ρ₁ ℓ h, adj_dg_of_ne_zero q ρ₂ ℓ h, hj]
  · rw [adj_dg_of_eq_zero q ρ₁ ℓ h, adj_dg_of_eq_zero q ρ₂ ℓ h, LinearMap.id_apply, LinearMap.id_apply]

private theorem natCast_ne_zero_dg (q : ℕ) [hqp : Fact q.Prime] {S₀ : Set ℕ} (hq : q ∈ S₀) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓS : ℓ ∉ S₀) : (ℓ : ZMod q) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact hℓS ((Nat.prime_dvd_prime_iff_eq hqp.out hℓ).1 h0 ▸ hq)

private theorem adj_dg_comp_heckeConj (N q : ℕ) [Fact q.Prime] {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K (CuspidalType.GL2 q) V) (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)
    {S₀ : Set ℕ} (hq : q ∈ S₀) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (_ : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S₀)
    (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    adj_dg q ρ ℓ ∘ₗ (ρ.comp red) (HeckeEis.heckeConj N ℓ u) = (ρ.comp red) (u : Gamma0 N) ∘ₗ adj_dg q ρ ℓ := by
  have h := natCast_ne_zero_dg q hq ℓ hℓ hℓS
  rw [adj_dg_of_ne_zero q ρ ℓ h]
  exact HeckeEis.diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero N q K ρ red hred ℓ h u

end DescentGlue

theorem solution
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (hq : q ∈ S₀) (b : ℕ → ℤ)
    (κ₀ : Type) [Field κ₀] [CharP κ₀ p]
    {V₀ : Type} [AddCommGroup V₀] [Module κ₀ V₀] [FiniteDimensional κ₀ V₀]
      (ρ₀ : Representation κ₀ (CuspidalType.GL2 q) V₀)
    (π₀ : ↥(CuspidalType.steinberg q κ₀).toSubmodule →ₗ[κ₀] V₀)
    (hπ₀ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ₀).toSubmodule,
        π₀ ⟨CuspidalType.ind q κ₀ g v, (CuspidalType.steinberg q κ₀).apply_mem_toSubmodule g v.2⟩ = ρ₀ g (π₀ v))
    (hπ₀surj : Function.Surjective π₀)
    (hπ₀ker : ∀ v : ↥(CuspidalType.steinberg q κ₀).toSubmodule,
        π₀ v = 0 ↔ ∃ c : κ₀, (v : CuspidalType.ProjLine q →₀ κ₀) = c • CuspidalType.constFun q κ₀)
    (h₀ : HeckeEis.IsEigensystemH1 N (ρ₀.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then ρ₀ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        S₀ (fun ℓ => ((b ℓ : ℤ) : κ₀)))
    (κ : Type) [Field κ] [CharP κ p]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
:
      HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        S₀ (fun ℓ => ((b ℓ : ℤ) : κ)) := by
  classical
  letI : Algebra (ZMod p) κ₀ := ZMod.algebra κ₀ p
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  set red : Gamma0 N →* CuspidalType.GL2 q := (Matrix.SpecialLinearGroup.toGL.comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype with hred
  change HeckeEis.IsEigensystemH1 N (ρ.comp red) (adj_dg q ρ) S₀ (fun ℓ => ((b ℓ : ℤ) : κ))
  change HeckeEis.IsEigensystemH1 N (ρ₀.comp red) (adj_dg q ρ₀) S₀ (fun ℓ => ((b ℓ : ℤ) : κ₀)) at h₀

  obtain ⟨W, _, _, _, ρW, πW, hπW, hπWsurj, hπWker⟩ :=
    CuspidalType.exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun q (ZMod p)
  obtain ⟨j₀, hj₀, d₀, bW₀, bV₀, hb₀⟩ :=
    CuspidalType.exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod
      p ρW πW hπW hπWsurj hπWker κ₀ ρ₀ π₀ hπ₀ hπ₀surj hπ₀ker
  obtain ⟨j, hj, d, bW, bV, hb⟩ :=
    CuspidalType.exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod
      p ρW πW hπW hπWsurj hπWker κ ρ π hπ hπsurj hπker

  have hlam₀ : (fun ℓ => ((b ℓ : ℤ) : κ₀)) = fun ℓ => algebraMap (ZMod p) κ₀ ((b ℓ : ℤ) : ZMod p) := by
    funext ℓ
    rw [map_intCast]
  have hlam : (fun ℓ => ((b ℓ : ℤ) : κ)) = fun ℓ => algebraMap (ZMod p) κ ((b ℓ : ℤ) : ZMod p) := by
    funext ℓ
    rw [map_intCast]
  rw [hlam₀] at h₀
  rw [hlam]

  have hF : HeckeEis.IsEigensystemH1 N (ρW.comp red) (adj_dg q ρW) S₀ (fun ℓ => ((b ℓ : ℤ) : ZMod p)) :=
    isEigensystemH1_descent_dc N (ρW.comp red) (ρ₀.comp red) j₀ (fun γ x => hj₀ (red γ) x) bW₀ bV₀ hb₀
      (adj_dg q ρW) (adj_dg q ρ₀) (fun ℓ x => map_adj_dg q (algebraMap (ZMod p) κ₀) ρW ρ₀ j₀ hj₀ ℓ x) S₀
      (fun ℓ _ hℓ hℓN hℓS u => adj_dg_comp_heckeConj N q ρW red hred hq ℓ hℓ hℓN hℓS u) _ h₀

  exact HeckeEis.isEigensystemH1_of_isEigensystemH1_of_isBaseChange N (algebraMap (ZMod p) κ) S₀ (ρW.comp red)
    (ρ.comp red) (adj_dg q ρW) (adj_dg q ρ)
    (fun ℓ _ hℓ hℓN hℓS u => adj_dg_comp_heckeConj N q ρ red hred hq ℓ hℓ hℓN hℓS u) j (fun γ v => hj (red γ) v)
    (fun ℓ v _ _ _ => map_adj_dg q (algebraMap (ZMod p) κ) ρW ρ j hj ℓ v) ⟨Fin d, bW, bV, fun s => hb s⟩ _ hF

end S_HeckeEis_isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP (solution)
