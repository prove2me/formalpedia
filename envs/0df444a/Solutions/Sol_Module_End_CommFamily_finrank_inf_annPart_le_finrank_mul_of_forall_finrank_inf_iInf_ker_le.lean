-- Prove2me | solution 1 for Module.End.CommFamily.finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/48b036e6-a0f8-5a08-b12c-e8e380e791eb

import Mathlib
import Definitions.Def_Module_CommFamilyAnnPart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace E4ABody

open Polynomial

theorem ker_aeval_prod_X_sub_C_le_iSup {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (g : Module.End K M) (s : Finset K) :
    LinearMap.ker (aeval g (∏ r ∈ s, (X - C r))) ≤
      ⨆ r ∈ s, LinearMap.ker (g - algebraMap K (Module.End K M) r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    simp only [Finset.prod_empty, map_one, LinearMap.mem_ker, Module.End.one_apply] at hv
    subst hv
    exact Submodule.zero_mem _
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    have hcop : IsCoprime (X - C a) (∏ r ∈ s, (X - C r)) := by
      refine IsCoprime.prod_right fun r hr => ?_
      exact pairwise_coprime_X_sub_C (K := K) Function.injective_id (by rintro rfl; exact has hr)
    rw [← sup_ker_aeval_eq_ker_aeval_mul_of_coprime g hcop]
    rw [Finset.iSup_insert]
    refine sup_le_sup ?_ ih
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    simpa [sub_eq_add_neg, Module.algebraMap_end_apply] using hv

theorem coe_aeval_restrict {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (g : Module.End K M) (A : Submodule K M) (hA : ∀ v ∈ A, g v ∈ A) (P : K[X]) (x : A) :
    ((aeval (g.restrict hA) P x : A) : M) = aeval g P (x : M) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul,
      Module.algebraMap_end_apply]
    congr 1
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl

theorem inf_ker_aeval_prod_le_iSup {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (g : Module.End K M) (A : Submodule K M) (hA : ∀ v ∈ A, g v ∈ A) (s : Finset K) :
    A ⊓ LinearMap.ker (aeval g (∏ r ∈ s, (X - C r))) ≤
      ⨆ r ∈ s, (A ⊓ LinearMap.ker (g - algebraMap K (Module.End K M) r)) := by
  classical
  intro v hv
  obtain ⟨hvA, hvk⟩ := Submodule.mem_inf.mp hv
  set g' := g.restrict hA with hg'
  have hx : (⟨v, hvA⟩ : A) ∈ LinearMap.ker (aeval g' (∏ r ∈ s, (X - C r))) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [coe_aeval_restrict]
    exact (LinearMap.mem_ker.mp hvk)
  have hx' := ker_aeval_prod_X_sub_C_le_iSup g' s hx
  have hmap : Submodule.map A.subtype (⨆ r ∈ s, LinearMap.ker (g' - algebraMap K (Module.End K A) r)) ≤
      ⨆ r ∈ s, (A ⊓ LinearMap.ker (g - algebraMap K (Module.End K M) r)) := by
    simp only [Submodule.map_iSup]
    refine iSup₂_mono fun r hr => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.mem_inf.mpr ⟨y.2, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hy
    rw [LinearMap.mem_ker]
    have := congrArg (fun z : A => (z : M)) hy
    simpa [hg', LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.restrict_apply] using this
  exact hmap ⟨⟨v, hvA⟩, hx', rfl⟩

end E4ABody

set_option maxHeartbeats 6400000 in
theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : Type*}
    (F : Module.End.CommFamily K V σ) (p : ℕ) [Fact p.Prime] [CharP K p]
    {k₀ : Type*} [Field k₀] [Finite k₀] [Algebra (ZMod p) k₀]
    (θ₀ : σ → k₀) (hgen : Algebra.adjoin (ZMod p) (Set.range θ₀) = ⊤) (e : k₀ →+* K)
    (W : Submodule K V) (hW : ∀ (a : σ) (v : V), v ∈ W → F.T a v ∈ W) (d : ℕ)
    (hd : ∀ τ : k₀ →+* K,
      FiniteDimensional K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ∧
        Module.finrank K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ≤ d) :
    FiniteDimensional K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ∧
      Module.finrank K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ≤ Module.finrank (ZMod p) k₀ * d := by
  classical
  set A : Submodule K V := W ⊓ F.annPart p (e ∘ θ₀) with hA
  let Eig : (k₀ →+* K) → Submodule K V :=
    fun τ => W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)
  let cK : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  haveI : Module.Finite (ZMod p) k₀ := Module.Finite.of_finite
  have hcK : cK = e.comp (algebraMap (ZMod p) k₀) := Subsingleton.elim _ _

  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) k₀
  have hγint : IsIntegral (ZMod p) γ := IsIntegral.of_finite (ZMod p) γ
  have hμdeg : (minpoly (ZMod p) γ).natDegree = Module.finrank (ZMod p) k₀ :=
    (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) γ).mp hγ

  obtain ⟨Pγ, hPγ⟩ : ∃ P : MvPolynomial σ (ZMod p), MvPolynomial.aeval θ₀ P = γ := by
    have hmem : γ ∈ Algebra.adjoin (ZMod p) (Set.range θ₀) := by rw [hgen]; exact Algebra.mem_top
    rw [Algebra.adjoin_range_eq_range_aeval] at hmem
    exact hmem
  have hQ : ∀ a : σ, ∃ Q : Polynomial (ZMod p), Polynomial.aeval γ Q = θ₀ a := by
    intro a
    have hmem : θ₀ a ∈ (IntermediateField.adjoin (ZMod p) {γ}).toSubalgebra := by
      rw [hγ]; exact Algebra.mem_top
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hγint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hmem
    exact hmem
  choose Q hQ using hQ

  set G : Module.End K V := F.eval (MvPolynomial.map cK Pγ) with hG
  have hann : ∀ (Qm : MvPolynomial σ (ZMod p)), MvPolynomial.aeval θ₀ Qm = 0 →
      ∀ v ∈ A, F.eval (MvPolynomial.map cK Qm) v = 0 := by
    intro Qm hQm v hv
    have hv2 := (Submodule.mem_inf.mp hv).2
    rw [Module.End.CommFamily.mem_annPart_iff] at hv2
    refine hv2 Qm ?_
    have : MvPolynomial.aeval (⇑e ∘ θ₀) (MvPolynomial.map cK Qm) = MvPolynomial.eval₂ cK (⇑e ∘ θ₀) Qm := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
      congr 1
    rw [this, hcK, ← MvPolynomial.eval₂_comp_left, ← MvPolynomial.aeval_def, hQm, map_zero]
  have hpoly : ∀ (q : Polynomial (ZMod p)),
      F.eval (MvPolynomial.map cK (Polynomial.aeval Pγ q)) = Polynomial.aeval G (q.map cK) := by
    intro q
    have h1 : (MvPolynomial.map cK) (Polynomial.aeval Pγ q) =
        Polynomial.aeval (MvPolynomial.map cK Pγ) (q.map cK) := by
      refine Polynomial.map_aeval_eq_aeval_map ?_ q Pγ
      ext r
      simp
    rw [h1, hG, ← Polynomial.aeval_algHom_apply]

  set μ : Polynomial (ZMod p) := minpoly (ZMod p) γ with hμ
  have hμmonic : μ.Monic := minpoly.monic hγint
  have hμsep : μ.Separable := Algebra.IsSeparable.isSeparable (ZMod p) γ
  have hμk_splits : (μ.map (algebraMap (ZMod p) k₀)).Splits :=
    Normal.splits (inferInstance : Normal (ZMod p) k₀) γ
  set μK : Polynomial K := μ.map cK with hμK
  have hμK_eq : μK = (μ.map (algebraMap (ZMod p) k₀)).map e := by
    rw [hμK, hcK, Polynomial.map_map]
  have hμK_splits : μK.Splits := by rw [hμK_eq]; exact hμk_splits.map e
  have hμK_monic : μK.Monic := hμmonic.map cK
  have hμK_sep : μK.Separable := hμsep.map
  have hμK_nodup : μK.roots.Nodup := Polynomial.nodup_roots hμK_sep
  set s : Finset K := μK.roots.toFinset with hs
  have hμK_prod : μK = ∏ r ∈ s, (Polynomial.X - Polynomial.C r) := by
    rw [Finset.prod_eq_multiset_prod, hs, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hμK_nodup]
    exact hμK_splits.eq_prod_roots_of_monic hμK_monic
  have hs_card : s.card ≤ Module.finrank (ZMod p) k₀ := by
    rw [hs, Multiset.toFinset_card_eq_card_iff_nodup.mpr hμK_nodup, ← hμK_splits.natDegree_eq_card_roots,
      hμK, Polynomial.natDegree_map, hμdeg]

  have hkill : ∀ v ∈ A, Polynomial.aeval G μK v = 0 := by
    intro v hv
    rw [hμK, ← hpoly]
    refine hann _ ?_ v hv
    rw [← Polynomial.aeval_algHom_apply, hPγ, hμ, minpoly.aeval]
  have hevalW : ∀ (Qm : MvPolynomial σ K), ∀ v ∈ W, F.eval Qm v ∈ W := by
    intro Qm
    have hmem := F.eval_mem_adjoin Qm
    refine Algebra.adjoin_induction (p := fun (g : Module.End K V) _ => ∀ v ∈ W, g v ∈ W)
      ?_ ?_ ?_ ?_ hmem
    · rintro g ⟨a, rfl⟩ v hv
      exact hW a v hv
    · intro r v hv
      simpa [Module.algebraMap_end_apply] using W.smul_mem r hv
    · intro x y _ _ hx hy v hv
      simpa using W.add_mem (hx v hv) (hy v hv)
    · intro x y _ _ hx hy v hv
      simpa using hx _ (hy v hv)
  have hevalAnn : ∀ (Qm : MvPolynomial σ K), ∀ v ∈ F.annPart p (e ∘ θ₀), F.eval Qm v ∈ F.annPart p (e ∘ θ₀) := by
    intro Qm v hv
    rw [Module.End.CommFamily.mem_annPart_iff] at hv ⊢
    intro Q' hQ'
    have hcomm : F.eval (MvPolynomial.map cK Q') * F.eval Qm = F.eval Qm * F.eval (MvPolynomial.map cK Q') := by
      rw [← map_mul, ← map_mul, mul_comm]
    have := congrArg (fun g : Module.End K V => g v) hcomm
    simp only [Module.End.mul_apply] at this
    rw [this, hv Q' hQ', map_zero]
  have hGA : ∀ v ∈ A, G v ∈ A := by
    intro v hv
    obtain ⟨hvW, hvAnn⟩ := Submodule.mem_inf.mp hv
    exact Submodule.mem_inf.mpr ⟨hevalW _ v hvW, hevalAnn _ v hvAnn⟩
  have hAle : A ≤ ⨆ r ∈ s, (A ⊓ LinearMap.ker (G - algebraMap K (Module.End K V) r)) := by
    intro v hv
    refine E4ABody.inf_ker_aeval_prod_le_iSup G A hGA s (Submodule.mem_inf.mpr ⟨hv, ?_⟩)
    rw [LinearMap.mem_ker, ← hμK_prod]
    exact hkill v hv

  have hroot : ∀ r ∈ s, ∃ τ : k₀ →+* K,
      A ⊓ LinearMap.ker (G - algebraMap K (Module.End K V) r) ≤ Eig τ := by
    intro r hr
    have hr' : r ∈ μK.roots := by rwa [hs, Multiset.mem_toFinset] at hr
    rw [hμK_eq, hμk_splits.roots_map_of_injective e.injective, Multiset.mem_map] at hr'
    obtain ⟨ρ, hρ, hρr⟩ := hr'

    have hρa : ρ ∈ (minpoly (ZMod p) γ).aroots k₀ := hρ
    obtain ⟨φ, hφγ⟩ : ∃ φ : k₀ →ₐ[ZMod p] k₀, φ γ = ρ := by
      let ι : k₀ ≃ₐ[ZMod p] ↥(IntermediateField.adjoin (ZMod p) ({γ} : Set k₀)) :=
        (IntermediateField.topEquiv (F := ZMod p) (E := k₀)).symm.trans
          (IntermediateField.equivOfEq hγ.symm)
      let φ₀ : ↥(IntermediateField.adjoin (ZMod p) ({γ} : Set k₀)) →ₐ[ZMod p] k₀ :=
        (IntermediateField.algHomAdjoinIntegralEquiv (ZMod p) (K := k₀) hγint).symm ⟨ρ, hρa⟩
      refine ⟨φ₀.comp (ι : k₀ →ₐ[ZMod p] ↥(IntermediateField.adjoin (ZMod p) ({γ} : Set k₀))), ?_⟩
      have hι : ι γ = IntermediateField.AdjoinSimple.gen (ZMod p) γ := Subtype.ext rfl
      have hφ₀ : φ₀ (IntermediateField.AdjoinSimple.gen (ZMod p) γ) = ρ :=
        IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen (ZMod p) (K := k₀) hγint ⟨ρ, hρa⟩
      change φ₀ (ι γ) = ρ
      rw [hι, hφ₀]
    refine ⟨e.comp φ.toRingHom, ?_⟩
    intro v hv
    obtain ⟨hvA, hvker⟩ := Submodule.mem_inf.mp hv
    have hGv : G v = r • v := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hvker
      rw [hvker]; rfl
    refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hvA).1, ?_⟩
    rw [Submodule.mem_iInf]
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

    have hQa : MvPolynomial.aeval θ₀ (MvPolynomial.X a - Polynomial.aeval Pγ (Q a)) = 0 := by
      rw [map_sub, MvPolynomial.aeval_X, ← Polynomial.aeval_algHom_apply, hPγ, hQ a, sub_self]
    have h1 := hann _ hQa v hvA
    rw [map_sub, map_sub, MvPolynomial.map_X, Module.End.CommFamily.eval_X, LinearMap.sub_apply,
      sub_eq_zero, hpoly] at h1
    rw [h1, Module.End.aeval_apply_of_mem_apply_eq_smul hGv]
    congr 1

    rw [← hρr, hcK, ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_hom]
    show e (Polynomial.eval ρ (Polynomial.map (algebraMap (ZMod p) k₀) (Q a))) = e (φ (θ₀ a))
    congr 1
    rw [Polynomial.eval_map_algebraMap]
    conv_rhs => rw [← hQ a, ← Polynomial.aeval_algHom_apply, hφγ]
  haveI : Nonempty (k₀ →+* K) := ⟨e⟩
  choose! τ hτ using hroot

  haveI : ∀ r, FiniteDimensional K ↥(Eig (τ r)) := fun r => (hd (τ r)).1
  have hAle' : A ≤ ⨆ r ∈ s, Eig (τ r) :=
    hAle.trans (iSup₂_mono fun r hr => hτ r hr)
  have hsup : (⨆ r ∈ s, Eig (τ r)) = s.sup (fun r => Eig (τ r)) := (Finset.sup_eq_iSup s _).symm
  rw [hsup] at hAle'
  haveI : FiniteDimensional K ↥(s.sup fun r => Eig (τ r)) := inferInstance
  have hfin : FiniteDimensional K ↥A := Submodule.finiteDimensional_of_le hAle'
  refine ⟨hfin, ?_⟩
  have hbound : ∀ t : Finset K, t ⊆ s →
      Module.finrank K ↥(t.sup fun r => Eig (τ r)) ≤ t.card * d := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t hat ih =>
      intro hsub
      rw [Finset.sup_insert, Finset.card_insert_of_notMem hat]
      calc Module.finrank K ↥(Eig (τ a) ⊔ t.sup fun r => Eig (τ r))
          ≤ Module.finrank K ↥(Eig (τ a)) + Module.finrank K ↥(t.sup fun r => Eig (τ r)) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ d + t.card * d := Nat.add_le_add (hd (τ a)).2 (ih (fun x hx => hsub (Finset.mem_insert_of_mem hx)))
        _ = (t.card + 1) * d := by ring
  calc Module.finrank K ↥A ≤ Module.finrank K ↥(s.sup fun r => Eig (τ r)) := Submodule.finrank_mono hAle'
    _ ≤ s.card * d := hbound s (Finset.Subset.refl s)
    _ ≤ Module.finrank (ZMod p) k₀ * d := Nat.mul_le_mul_right d hs_card

end S_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
end P2MW
export P2MW.S_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le (solution)
