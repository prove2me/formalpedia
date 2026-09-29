-- Prove2me | solution 1 for ModularCurve.iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/cde69b3f-66ef-5c23-8729-0a41abd50535

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good

set_option autoImplicit false

namespace C2bChi

open Module Module.End

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem isCompl_ker_range {f : End K V} (hf : f.IsSemisimple) : IsCompl (LinearMap.ker f) (LinearMap.range f) := by

  rw [isSemisimple_iff] at hf
  have hinv : LinearMap.range f ∈ invtSubmodule f := by
    rw [mem_invtSubmodule]
    rintro x -
    exact LinearMap.mem_range_self f x
  obtain ⟨q, hq, hc⟩ := hf _ hinv
  have hqker : q ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    have h1 : f x ∈ q := hq hx
    have h2 : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    have := hc.symm.disjoint.le_bot (Submodule.mem_inf.mpr ⟨h1, h2⟩)
    simpa using this
  have hdim : finrank K q = finrank K (LinearMap.ker f) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 := LinearMap.finrank_range_add_finrank_ker f
    omega
  have hq_eq : q = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hqker hdim
  rw [← hq_eq]
  exact hc.symm

theorem exists_proj {f : End K V} (hf : f.IsSemisimple) :
    ∃ π : End K V, (∀ x, π x ∈ LinearMap.ker f) ∧ (∀ x ∈ LinearMap.ker f, π x = x) ∧
      (∀ x ∈ LinearMap.range f, π x = 0) ∧ ∀ g : End K V, Commute f g → ∀ x, π (g x) = g (π x) := by
  have hc := isCompl_ker_range hf
  let π : End K V := (LinearMap.ker f).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hc
  have hleft : ∀ x ∈ LinearMap.ker f, π x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)
  have hright : ∀ x ∈ LinearMap.range f, π x = 0 := fun x hx => by
    have := Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩
    exact (congrArg Subtype.val this).trans rfl
  refine ⟨π, fun x => Submodule.coe_mem _, hleft, hright, fun g hg x => ?_⟩
  ·
    have hx : x ∈ LinearMap.ker f ⊔ LinearMap.range f := by rw [hc.codisjoint.eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    have hgk : g k ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker] at hk ⊢
      rw [← Module.End.mul_apply, hg.eq, Module.End.mul_apply, hk, map_zero]
    have hgr : g r ∈ LinearMap.range f := by
      obtain ⟨y, rfl⟩ := hr
      exact ⟨g y, by rw [← Module.End.mul_apply, hg.eq, Module.End.mul_apply]⟩
    rw [map_add, map_add, map_add, hleft k hk, hright r hr, hleft _ hgk, hright _ hgr, add_zero, add_zero]

theorem eq_zero_of_mem_ker_of_eq_sum {ι : Type} (s : Finset ι) (f : ι → End K V)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hss : ∀ i ∈ s, (f i).IsSemisimple) :
    ∀ (x : V) (y : ι → V), (∀ i ∈ s, f i x = 0) → x = ∑ i ∈ s, f i (y i) → x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x y _ hx; simpa using hx
  | @insert a s ha ih =>
    intro x y hker hx
    obtain ⟨π, hπker, hπid, hπrange, hπcomm⟩ := exists_proj (hss a (Finset.mem_insert_self a s))

    have hxa : x ∈ LinearMap.ker (f a) := hker a (Finset.mem_insert_self a s)
    have hx' : x = ∑ i ∈ s, f i (π (y i)) := by
      conv_lhs => rw [← hπid x hxa, hx, Finset.sum_insert ha, map_add, hπrange _ (LinearMap.mem_range_self _ _), zero_add,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact hπcomm (f i) (hcomm a i) (y i)
    exact ih (fun i hi => hss i (Finset.mem_insert_of_mem hi)) x (fun i => π (y i))
      (fun i hi => hker i (Finset.mem_insert_of_mem hi)) hx'

end C2bChi

set_option autoImplicit false
open scoped TensorProduct

namespace C2bChi

open Module Module.End

section Setup

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]

noncomputable abbrev Th (t : ModularCurve.HeckeAlgOne) : End K (K ⊗[ℤ_[p]] TateModule p J) :=
  (ModularCurve.tateHeckeRepOne p J t).baseChange K

theorem Th_mul (s t : ModularCurve.HeckeAlgOne) : Th p J K (s * t) = Th p J K s * Th p J K t := by
  rw [Th, map_mul, LinearMap.baseChange_mul]

theorem Th_comm (s t : ModularCurve.HeckeAlgOne) : Commute (Th p J K s) (Th p J K t) := by
  show Th p J K s * Th p J K t = Th p J K t * Th p J K s
  rw [← Th_mul, ← Th_mul, mul_comm]

variable (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p J) →+* K)

noncomputable def lam (t : ModularCurve.HeckeAlgOne) : K :=
  Λ ⟨ModularCurve.rationalHeckeRepOne p J t, ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩

theorem lam_mul (s t : ModularCurve.HeckeAlgOne) : lam p J K Λ (s * t) = lam p J K Λ s * lam p J K Λ t := by
  rw [lam, lam, lam, ← map_mul]
  congr 1
  exact Subtype.ext (map_mul _ s t)

theorem lam_one : lam p J K Λ 1 = 1 := by
  rw [lam, ← Λ.map_one]
  congr 1
  exact Subtype.ext (map_one _)

noncomputable def lamHom : ModularCurve.HeckeAlgOne →* K where
  toFun := lam p J K Λ
  map_one' := lam_one p J K Λ
  map_mul' := lam_mul p J K Λ

theorem lam_eq_of_mul_eq {s t u : ModularCurve.HeckeAlgOne}
    (h : ModularCurve.tateHeckeRepOne p J s * ModularCurve.tateHeckeRepOne p J t = ModularCurve.tateHeckeRepOne p J u) :
    lam p J K Λ s * lam p J K Λ t = lam p J K Λ u := by
  rw [← lam_mul, lam, lam]
  congr 2
  rw [map_mul, ModularCurve.rationalHeckeRepOne_apply, ModularCurve.rationalHeckeRepOne_apply,
    ModularCurve.rationalHeckeRepOne_apply, ← LinearMap.baseChange_mul, h]

theorem Th_eq_of_mul_eq {s t u : ModularCurve.HeckeAlgOne}
    (h : ModularCurve.tateHeckeRepOne p J s * ModularCurve.tateHeckeRepOne p J t = ModularCurve.tateHeckeRepOne p J u) :
    Th p J K s * Th p J K t = Th p J K u := by
  rw [← Th_mul, Th, map_mul, h]

theorem isSemisimple_Th {w : ModularCurve.HeckeAlgOne} {P : Polynomial ℤ} (hsepP : (P.map (Int.castRingHom ℚ)).Separable)
    (hP : Polynomial.aeval (ModularCurve.tateHeckeRepOne p J w) P = 0) : (Th p J K w).IsSemisimple := by
  apply isSemisimple_of_squarefree_aeval_eq_zero (p := P.map (algebraMap ℤ K))
  · have : P.map (algebraMap ℤ K) = (P.map (Int.castRingHom ℚ)).map (algebraMap ℚ K) := by
      rw [Polynomial.map_map]
      congr 1
      ext n
      simp
    rw [this]
    exact hsepP.map.squarefree
  · rw [Polynomial.aeval_map_algebraMap]
    have h1 : Th p J K w = Module.End.baseChangeHom ℤ_[p] K (TateModule p J) (ModularCurve.tateHeckeRepOne p J w) := rfl
    rw [h1, ← Polynomial.aeval_map_algebraMap ℤ_[p], Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap, hP,
      map_zero]

end Setup

theorem main
    (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p J) →+* K)
    (hΛ : ∀ c : ℤ_[p],
      Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p J) (c : ℚ_[p])) = algebraMap ℤ_[p] K c)
    (G : Set ModularCurve.HeckeAlgOne)
    (hsep : ∀ w ∈ Algebra.adjoin ℤ G, ∃ P : Polynomial ℤ, P ≠ 0 ∧ (P.map (Int.castRingHom ℚ)).Separable ∧
      Polynomial.aeval (ModularCurve.tateHeckeRepOne p J w) P = 0)
    (hgood : ∀ t : ModularCurve.HeckeAlgOne, ∃ s ∈ Algebra.adjoin ℤ G, ∃ u ∈ Algebra.adjoin ℤ G,
      Λ ⟨ModularCurve.rationalHeckeRepOne p J s,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J s⟩ ≠ 0 ∧
      ModularCurve.tateHeckeRepOne p J s * ModularCurve.tateHeckeRepOne p J t = ModularCurve.tateHeckeRepOne p J u) :
    (⨅ t : ModularCurve.HeckeAlgOne,
        LinearMap.ker ((ModularCurve.tateHeckeRepOne p J t).baseChange K - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • LinearMap.id)) ⊓
      Submodule.span K
        {z : K ⊗[ℤ_[p]] TateModule p J |
          ∃ (t : ModularCurve.HeckeAlgOne) (y : K ⊗[ℤ_[p]] TateModule p J),
            z = (ModularCurve.tateHeckeRepOne p J t).baseChange K y - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • y} = ⊥ := by
  classical
  haveI : Module.Finite K (K ⊗[ℤ_[p]] TateModule p J) := inferInstance
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxE, hxP⟩ := Submodule.mem_inf.mp hx

  have hE : ∀ t : ModularCurve.HeckeAlgOne, Th p J K t x = lam p J K Λ t • x := by
    intro t
    have := (Submodule.mem_iInf _).mp hxE t
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this

  obtain ⟨n, c, z, hz⟩ := Submodule.mem_span_set'.mp hxP
  have hzi : ∀ i : Fin n, ∃ (t : ModularCurve.HeckeAlgOne) (y : K ⊗[ℤ_[p]] TateModule p J),
      c i • (z i : K ⊗[ℤ_[p]] TateModule p J) = Th p J K t y - lam p J K Λ t • y := by
    intro i
    obtain ⟨t, y, hy⟩ := (z i).2
    refine ⟨t, c i • y, ?_⟩
    rw [hy, smul_sub, map_smul, smul_comm]
    rfl
  choose t y hty using hzi

  have hg : ∀ i : Fin n, ∃ s ∈ Algebra.adjoin ℤ G, ∃ u ∈ Algebra.adjoin ℤ G, lam p J K Λ s ≠ 0 ∧
      ModularCurve.tateHeckeRepOne p J s * ModularCurve.tateHeckeRepOne p J (t i) = ModularCurve.tateHeckeRepOne p J u :=
    fun i => hgood (t i)
  choose s hs u hu hls hstu using hg

  let S : ModularCurve.HeckeAlgOne := ∏ i, s i
  let g : Fin n → ModularCurve.HeckeAlgOne := fun i => ∏ j ∈ Finset.univ.erase i, s j
  have hSg : ∀ i, S = s i * g i := fun i => (Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)).symm
  have hlS : lam p J K Λ S ≠ 0 := by
    show lamHom p J K Λ (∏ i, s i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hls i

  let F : ModularCurve.HeckeAlgOne → End K (K ⊗[ℤ_[p]] TateModule p J) := fun w => Th p J K w - lam p J K Λ w • 1
  have hFcomm : ∀ a b, Commute (F a) (F b) := by
    intro a b
    rw [commute_iff_eq]
    refine LinearMap.ext fun x => ?_
    have hc := congrArg (fun f => f x) (Th_comm p J K a b).eq
    simp only [Module.End.mul_apply] at hc
    simp only [F, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, hc]
    module
  have hFss : ∀ w ∈ Algebra.adjoin ℤ G, (F w).IsSemisimple := by
    intro w hw
    obtain ⟨P, -, hPsep, hP0⟩ := hsep w hw
    have h1 := isSemisimple_Th p J K hPsep hP0
    have : F w = Th p J K w - algebraMap K (End K (K ⊗[ℤ_[p]] TateModule p J)) (lam p J K Λ w) := by
      rw [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Module.End.isSemisimple_sub_algebraMap_iff.mpr h1
  have hFx : ∀ w, F w x = 0 := by
    intro w
    simp only [F, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hE w, sub_self]

  have hx1 : x = ∑ i, (Th p J K (t i) (y i) - lam p J K Λ (t i) • y i) := by
    rw [← hz]; exact Finset.sum_congr rfl fun i _ => hty i
  have key : ∀ i, Th p J K S (Th p J K (t i) (y i) - lam p J K Λ (t i) • y i) =
      F (u i) (Th p J K (g i) (y i)) + F (s i) (-(lam p J K Λ (t i)) • Th p J K (g i) (y i)) := by
    intro i
    have hlu : lam p J K Λ (s i) * lam p J K Λ (t i) = lam p J K Λ (u i) := lam_eq_of_mul_eq p J K Λ (hstu i)
    have hTu : Th p J K (s i) * Th p J K (t i) = Th p J K (u i) := Th_eq_of_mul_eq p J K (hstu i)

    have L : Th p J K S (Th p J K (t i) (y i) - lam p J K Λ (t i) • y i) =
        Th p J K (g i) (Th p J K (u i) (y i)) - lam p J K Λ (t i) • Th p J K (g i) (Th p J K (s i) (y i)) := by
      rw [hSg i, Th_mul, (Th_comm p J K (s i) (g i)).eq, map_sub, map_smul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (Th p J K (s i)) (Th p J K (t i)), hTu]
    have c1 : Th p J K (u i) (Th p J K (g i) (y i)) = Th p J K (g i) (Th p J K (u i) (y i)) := by
      rw [← Module.End.mul_apply, (Th_comm p J K (u i) (g i)).eq, Module.End.mul_apply]
    have c2 : Th p J K (s i) (Th p J K (g i) (y i)) = Th p J K (g i) (Th p J K (s i) (y i)) := by
      rw [← Module.End.mul_apply, (Th_comm p J K (s i) (g i)).eq, Module.End.mul_apply]
    have R : F (u i) (Th p J K (g i) (y i)) + F (s i) (-(lam p J K Λ (t i)) • Th p J K (g i) (y i)) =
        Th p J K (g i) (Th p J K (u i) (y i)) - lam p J K Λ (t i) • Th p J K (g i) (Th p J K (s i) (y i)) := by
      simp only [F, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul, map_neg, c1, c2, ← hlu]
      module
    exact L.trans R.symm
  have hx2 : lam p J K Λ S • x =
      ∑ i, (F (u i) (Th p J K (g i) (y i)) + F (s i) (-(lam p J K Λ (t i)) • Th p J K (g i) (y i))) := by
    rw [← hE S, hx1, map_sum]
    exact Finset.sum_congr rfl fun i _ => key i

  let w : Fin n ⊕ Fin n → ModularCurve.HeckeAlgOne := Sum.elim u s
  let Y : Fin n ⊕ Fin n → K ⊗[ℤ_[p]] TateModule p J :=
    Sum.elim (fun i => (lam p J K Λ S)⁻¹ • Th p J K (g i) (y i))
      (fun i => (lam p J K Λ S)⁻¹ • (-(lam p J K Λ (t i)) • Th p J K (g i) (y i)))
  have hx3 : x = ∑ k, F (w k) (Y k) := by
    rw [Fintype.sum_sum_type]
    simp only [w, Y, Sum.elim_inl, Sum.elim_inr, map_smul]
    simp only [map_smul] at hx2
    rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, ← Finset.sum_add_distrib, ← hx2, smul_smul,
      inv_mul_cancel₀ hlS, one_smul]
  exact eq_zero_of_mem_ker_of_eq_sum Finset.univ (fun k => F (w k)) (fun k k' => hFcomm _ _)
    (fun k _ => hFss (w k) (by rcases k with i | i; exacts [hu i, hs i])) x Y (fun k _ => hFx (w k)) hx3

end C2bChi

theorem solution
    (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p J) →+* K)
    (hΛ : ∀ c : ℤ_[p],
      Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p J) (c : ℚ_[p])) = algebraMap ℤ_[p] K c)
    (G : Set ModularCurve.HeckeAlgOne)
    (hsep : ∀ w ∈ Algebra.adjoin ℤ G, ∃ P : Polynomial ℤ, P ≠ 0 ∧ (P.map (Int.castRingHom ℚ)).Separable ∧
      Polynomial.aeval (ModularCurve.tateHeckeRepOne p J w) P = 0)
    (hgood : ∀ t : ModularCurve.HeckeAlgOne, ∃ s ∈ Algebra.adjoin ℤ G, ∃ u ∈ Algebra.adjoin ℤ G,
      Λ ⟨ModularCurve.rationalHeckeRepOne p J s,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J s⟩ ≠ 0 ∧
      ModularCurve.tateHeckeRepOne p J s * ModularCurve.tateHeckeRepOne p J t = ModularCurve.tateHeckeRepOne p J u) :
    (⨅ t : ModularCurve.HeckeAlgOne,
        LinearMap.ker ((ModularCurve.tateHeckeRepOne p J t).baseChange K - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • LinearMap.id)) ⊓
      Submodule.span K
        {z : K ⊗[ℤ_[p]] TateModule p J |
          ∃ (t : ModularCurve.HeckeAlgOne) (y : K ⊗[ℤ_[p]] TateModule p J),
            z = (ModularCurve.tateHeckeRepOne p J t).baseChange K y - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • y} = ⊥ :=
  C2bChi.main p J K Λ hΛ G hsep hgood

end S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good
end P2MW
export P2MW.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good (solution)
