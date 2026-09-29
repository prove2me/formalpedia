-- Prove2me | solution 1 for HopfAlgebra.withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c79de8af-0bf0-5e43-b9d5-46447b6f5bcc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem

set_option autoImplicit false

p2m_open "Coalgebra TensorProduct Coalgebra.TensorProduct Module WithConv"

universe u v w

namespace P2mAffineTorsionUnip

section LinAlg

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem exists_common_eigenvector [IsAlgClosed k]
    (S : Set (Module.End k V)) (hS : ∀ f ∈ S, ∀ g ∈ S, Commute f g) :
    ∀ (n : ℕ) (p : Submodule k V), FiniteDimensional k p → Module.finrank k p = n → p ≠ ⊥ →
      (∀ f ∈ S, ∀ v ∈ p, f v ∈ p) →
      ∃ v ∈ p, v ≠ 0 ∧ ∀ f ∈ S, ∃ c : k, f v = c • v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hfd hn hp hstab
  by_cases hscalar : ∀ f ∈ S, ∃ c : k, ∀ v ∈ p, f v = c • v
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    exact ⟨v, hv, hv0, fun f hf => (hscalar f hf).imp fun c hc => hc v hv⟩
  · push Not at hscalar
    obtain ⟨f, hfS, hf⟩ := hscalar
    haveI := hfd
    haveI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
    let fp : Module.End k p := f.restrict (fun v hv => hstab f hfS v hv)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue fp
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    let p' : Submodule k V := p ⊓ LinearMap.ker (f - μ • LinearMap.id)
    have hp'le : p' ≤ p := inf_le_left
    have hmem : ∀ v : V, v ∈ p' ↔ v ∈ p ∧ f v = μ • v := by
      intro v
      simp only [p', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hp'ne : p' ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      refine ⟨(w : V), (hmem w).mpr ⟨w.2, ?_⟩, fun h0 => hw.2 (Subtype.ext h0)⟩
      have h1 := hw.apply_eq_smul
      have h2 : ((fp w : p) : V) = f w := rfl
      rw [← h2, h1]
      rfl
    have hp'lt : p' < p := by
      obtain ⟨v, hv, hvne⟩ := hf μ
      refine lt_of_le_of_ne hp'le ?_
      intro heq
      exact hvne ((hmem v).mp (heq ▸ hv)).2
    haveI : FiniteDimensional k p' := Submodule.finiteDimensional_of_le hp'le
    have hlt : Module.finrank k p' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hp'lt
    have hstab' : ∀ g ∈ S, ∀ v ∈ p', g v ∈ p' := by
      intro g hg v hv
      obtain ⟨hvp, hfv⟩ := (hmem v).mp hv
      refine (hmem _).mpr ⟨hstab g hg v hvp, ?_⟩
      have hc := hS f hfS g hg
      calc f (g v) = g (f v) := by
            change (f * g) v = (g * f) v
            rw [hc.eq]
        _ = μ • g v := by rw [hfv, map_smul]
    obtain ⟨v, hv, hv0, hev⟩ := ih _ hlt p' inferInstance rfl hp'ne hstab'
    exact ⟨v, hp'le hv, hv0, hev⟩

theorem tmul_eq_zero_of_forall_lTensor {M : Type v} {N : Type w} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (t : M ⊗[k] N)
    (h : ∀ ξ : N →ₗ[k] k, LinearMap.lTensor M ξ t = 0) : t = 0 := by
  classical
  let 𝒞 := Module.Free.chooseBasis k N
  apply (TensorProduct.equivFinsuppOfBasisRight (M := M) 𝒞).injective
  rw [map_zero]
  ext i
  have key : ∀ s : M ⊗[k] N, (TensorProduct.equivFinsuppOfBasisRight (M := M) 𝒞 s) i =
      TensorProduct.rid k M (LinearMap.lTensor M (𝒞.coord i) s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
        rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, LinearMap.lTensor_tmul,
          TensorProduct.rid_tmul]
        rfl
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  rw [key, h, map_zero, Finsupp.zero_apply]

end LinAlg

section Rho

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H]

noncomputable def rho (ξ : H →ₗ[k] k) : H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H ξ ∘ₗ Coalgebra.comul

variable {k H}

theorem rho_apply (ξ : H →ₗ[k] k) (a : H) :
    rho k H ξ a = TensorProduct.rid k H (LinearMap.lTensor H ξ (Coalgebra.comul a)) := rfl

theorem rho_apply_repr (ξ : H →ₗ[k] k) {a : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr k a ι𝓡) :
    rho k H ξ a = ∑ i ∈ 𝓡.index, ξ (𝓡.right i) • 𝓡.left i := by
  rw [rho_apply, ← 𝓡.eq]
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

theorem rho_counit (a : H) : rho k H (Coalgebra.counit) a = a := by
  rw [rho_apply_repr _ (ℛ k a)]
  have h := sum_tmul_counit_eq (R := k) (ℛ k a)
  have := congrArg (TensorProduct.rid k H) h
  simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using this

theorem rho_convOne : rho k H (1 : WithConv (H →ₗ[k] k)).ofConv = LinearMap.id := by
  ext a
  rw [LinearMap.convOne_def]
  change rho k H (Algebra.linearMap k k ∘ₗ Coalgebra.counit) a = a
  have : (Algebra.linearMap k k ∘ₗ (Coalgebra.counit : H →ₗ[k] k)) = Coalgebra.counit := by
    ext x; simp
  rw [this, rho_counit]

theorem rho_convMul (ξ ξ' : WithConv (H →ₗ[k] k)) :
    rho k H (ξ * ξ').ofConv = rho k H ξ.ofConv ∘ₗ rho k H ξ'.ofConv := by
  ext a
  let 𝓡 := ℛ k a
  let a₁ := fun (i : 𝓡.ι) => ℛ k (𝓡.left i)
  let a₂ := fun (i : 𝓡.ι) => ℛ k (𝓡.right i)
  have hco := sum_tmul_tmul_eq 𝓡 a₁ a₂

  let Φ : H ⊗[k] (H ⊗[k] H) →ₗ[k] H :=
    (TensorProduct.rid k H).toLinearMap ∘ₗ
      LinearMap.lTensor H (LinearMap.mul' k k ∘ₗ TensorProduct.map ξ.ofConv ξ'.ofConv)
  have hΦ : ∀ x y z : H, Φ (x ⊗ₜ (y ⊗ₜ z)) = (ξ.ofConv y * ξ'.ofConv z) • x := by
    intro x y z
    simp only [Φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.rid_tmul]
  have h2 := congrArg Φ hco
  simp only [map_sum, hΦ] at h2

  rw [rho_apply_repr _ 𝓡]
  have hL : ∀ i ∈ 𝓡.index, (ξ * ξ').ofConv (𝓡.right i) • 𝓡.left i =
      ∑ j ∈ (a₂ i).index, (ξ.ofConv ((a₂ i).left j) * ξ'.ofConv ((a₂ i).right j)) • 𝓡.left i := by
    intro i _
    rw [← Finset.sum_smul]
    congr 1
    exact (a₂ i).convMul_apply ξ ξ'
  rw [Finset.sum_congr rfl hL, ← h2]

  rw [LinearMap.comp_apply, rho_apply_repr _ 𝓡, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rho_apply_repr _ (a₁ i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

noncomputable def rhoHom : WithConv (H →ₗ[k] k) →* Module.End k H where
  toFun ξ := rho k H ξ.ofConv
  map_one' := rho_convOne
  map_mul' ξ ξ' := by
    rw [Module.End.mul_eq_comp]
    exact rho_convMul ξ ξ'

theorem rhoHom_apply (ξ : WithConv (H →ₗ[k] k)) : rhoHom ξ = rho k H ξ.ofConv := rfl

theorem counit_rho (ξ : H →ₗ[k] k) (a : H) : Coalgebra.counit (rho k H ξ a) = ξ a := by
  rw [rho_apply_repr _ (ℛ k a), map_sum]
  simp only [map_smul, smul_eq_mul]
  have h := sum_counit_smul (R := k) (ℛ k a)
  calc ∑ i ∈ (ℛ k a).index, ξ ((ℛ k a).right i) * Coalgebra.counit ((ℛ k a).left i)
      = ξ (∑ i ∈ (ℛ k a).index, Coalgebra.counit (R := k) ((ℛ k a).left i) • (ℛ k a).right i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
    _ = ξ a := by rw [h]

noncomputable def orbit (a : H) : Submodule k H :=
  Submodule.span k (Set.range fun ξ : H →ₗ[k] k => rho k H ξ a)

theorem rho_mem_orbit_gen (ξ : H →ₗ[k] k) (a : H) : rho k H ξ a ∈ orbit (k := k) a :=
  Submodule.subset_span ⟨ξ, rfl⟩

theorem self_mem_orbit (a : H) : a ∈ orbit (k := k) a := by
  have := rho_mem_orbit_gen (k := k) (Coalgebra.counit) a
  rwa [rho_counit] at this

theorem orbit_le_span (a : H) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr k a ι𝓡) :
    orbit (k := k) a ≤ Submodule.span k (𝓡.left '' (𝓡.index : Set 𝓡.ι)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ξ, rfl⟩
  change rho k H ξ a ∈ _
  rw [rho_apply_repr _ 𝓡]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨i, hi, rfl⟩

scoped instance orbit_finiteDimensional (a : H) : FiniteDimensional k (orbit (k := k) a) := by
  let 𝓡 := ℛ k a
  have hfin : (𝓡.left '' (𝓡.index : Set 𝓡.ι)).Finite := (Finset.finite_toSet _).image _
  haveI : FiniteDimensional k (Submodule.span k (𝓡.left '' (𝓡.index : Set 𝓡.ι))) :=
    FiniteDimensional.span_of_finite k hfin
  exact Submodule.finiteDimensional_of_le (orbit_le_span a 𝓡)

theorem rho_mem_orbit (ξ : H →ₗ[k] k) {a v : H} (hv : v ∈ orbit (k := k) a) :
    rho k H ξ v ∈ orbit (k := k) a := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨ξ', rfl⟩ := hx
      have : rho k H ξ (rho k H ξ' a) = rho k H (toConv ξ * toConv ξ').ofConv a := by
        rw [rho_convMul]; rfl
      rw [this]
      exact rho_mem_orbit_gen _ a
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem exists_isGroupLikeElem_of_common_eigenvector {w : H} (hw : w ≠ 0)
    (hev : ∀ ξ : H →ₗ[k] k, ∃ c : k, rho k H ξ w = c • w) :
    ∃ b : H, IsGroupLikeElem k b ∧ ∀ ξ : H →ₗ[k] k, rho k H ξ w = ξ b • w := by
  obtain ⟨θ, hθ⟩ := Module.Projective.exists_dual_eq_one k hw
  let 𝓡 := ℛ k w
  let b : H := ∑ i ∈ 𝓡.index, θ (𝓡.left i) • 𝓡.right i
  have hb : ∀ ξ : H →ₗ[k] k, rho k H ξ w = ξ b • w := by
    intro ξ
    obtain ⟨c, hc⟩ := hev ξ
    have hξb : ξ b = c := by
      have h1 : θ (rho k H ξ w) = c := by rw [hc, map_smul, hθ, smul_eq_mul, mul_one]
      rw [← h1, rho_apply_repr _ 𝓡, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [hξb, hc]
  refine ⟨b, ?_, hb⟩

  have hΔ : Coalgebra.comul (R := k) w = w ⊗ₜ[k] b := by
    rw [← sub_eq_zero]
    apply tmul_eq_zero_of_forall_lTensor
    intro ξ
    rw [map_sub, sub_eq_zero]
    apply (TensorProduct.rid k H).injective
    rw [← rho_apply, hb ξ, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

  have hε : Coalgebra.counit (R := k) b = 1 := by
    have h1 := hb Coalgebra.counit
    rw [rho_counit] at h1
    have h2 : (Coalgebra.counit (R := k) b - 1) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw
  refine ⟨hε, ?_⟩

  have hco := Coalgebra.coassoc_apply (R := k) w
  rw [hΔ, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hΔ, TensorProduct.assoc_tmul] at hco

  have h3 : w ⊗ₜ[k] (Coalgebra.comul (R := k) b - b ⊗ₜ[k] b) = 0 := by
    rw [TensorProduct.tmul_sub, hco, sub_self]
  have h4 := congrArg (fun t => TensorProduct.lid k _ (LinearMap.rTensor _ θ t)) h3
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hθ, one_smul, map_zero] at h4
  exact (sub_eq_zero.mp h4)

theorem main [IsAlgClosed k] [Coalgebra.IsCocomm k H]
    (φ : WithConv (H →ₐ[k] k)) (m : ℕ) (hm : (m : k) ≠ 0) (hφ : φ ^ m = 1)
    (h1 : ∀ g : H, IsGroupLikeElem k g → φ g = 1) : φ = 1 := by

  let ψ : WithConv (H →ₗ[k] k) := toConv φ.ofConv.toLinearMap
  have hψ : ψ ^ m = 1 := by
    change (toConv φ.ofConv.toLinearMap) ^ m = 1
    rw [← AlgHom.toLinearMap_convPow, hφ, AlgHom.toLinearMap_convOne]
  let R : Module.End k H := rhoHom ψ
  have hRψ : R = rho k H φ.ofConv.toLinearMap := rfl
  have hRm : R ^ m = 1 := by
    change (rhoHom ψ) ^ m = 1
    rw [← map_pow, hψ, map_one]
  have hcomm : ∀ ξ : H →ₗ[k] k, rho k H ξ ∘ₗ R = R ∘ₗ rho k H ξ := by
    intro ξ
    change rhoHom (toConv ξ) * rhoHom ψ = rhoHom ψ * rhoHom (toConv ξ)
    rw [← map_mul, ← map_mul, mul_comm]

  have key : ∀ (μ : k) (v : H), v ≠ 0 → R v = μ • v → μ = 1 := by
    intro μ v hv hRv
    let W := orbit (k := k) v
    have hWeig : ∀ x ∈ W, R x = μ • x := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨ξ, rfl⟩ := hx
          calc R (rho k H ξ v) = rho k H ξ (R v) := by
                rw [← LinearMap.comp_apply, ← hcomm ξ, LinearMap.comp_apply]
            _ = μ • rho k H ξ v := by rw [hRv, map_smul]
      | zero => rw [map_zero, smul_zero]
      | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
      | smul c x _ hx => rw [map_smul, hx, smul_comm]

    let S : Set (Module.End k H) := Set.range (rho k H)
    have hS : ∀ f ∈ S, ∀ g ∈ S, Commute f g := by
      rintro _ ⟨ξ, rfl⟩ _ ⟨ξ', rfl⟩
      change rhoHom (toConv ξ) * rhoHom (toConv ξ') = rhoHom (toConv ξ') * rhoHom (toConv ξ)
      rw [← map_mul, ← map_mul, mul_comm]
    have hstab : ∀ f ∈ S, ∀ x ∈ W, f x ∈ W := by
      rintro _ ⟨ξ, rfl⟩ x hx
      exact rho_mem_orbit ξ hx
    have hWne : W ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨v, self_mem_orbit v, hv⟩
    obtain ⟨w, hwW, hw0, hev⟩ :=
      exists_common_eigenvector S hS _ W inferInstance rfl hWne hstab
    have hev' : ∀ ξ : H →ₗ[k] k, ∃ c : k, rho k H ξ w = c • w := fun ξ => hev _ ⟨ξ, rfl⟩
    obtain ⟨b, hb, hbev⟩ := exists_isGroupLikeElem_of_common_eigenvector hw0 hev'
    have hφb : φ b = 1 := h1 b hb
    have e1 : R w = w := by
      rw [hRψ, hbev]
      change φ b • w = w
      rw [hφb, one_smul]
    have e2 : R w = μ • w := hWeig w hwW
    have e3 : (μ - 1) • w = 0 := by rw [sub_smul, one_smul, ← e2, e1, sub_self]
    rcases smul_eq_zero.mp e3 with h | h
    · exact (sub_eq_zero.mp h)
    · exact absurd h hw0

  have hRid : ∀ a : H, R a = a := by
    intro a
    let W := orbit (k := k) a
    have hWst : ∀ x ∈ W, R x ∈ W := fun x hx => rho_mem_orbit _ hx
    let T : Module.End k W := R.restrict hWst
    have hTm : T ^ m = 1 := by
      rw [Module.End.pow_restrict m hWst]
      ext ⟨x, hx⟩
      simp [LinearMap.restrict_apply, hRm]

    have hsep : Squarefree (Polynomial.X ^ m - Polynomial.C (1 : k)) :=
      (Polynomial.separable_X_pow_sub_C (1 : k) hm one_ne_zero).squarefree
    have haev : Polynomial.aeval T (Polynomial.X ^ m - Polynomial.C (1 : k)) = 0 := by
      simp [hTm]
    have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep haev
    have hss1 : (T - algebraMap k (Module.End k W) 1).IsSemisimple :=
      (Module.End.isSemisimple_sub_algebraMap_iff).mpr hss
    have hT1 : T - algebraMap k (Module.End k W) 1 = 0 := by
      rw [hss1.eq_zero_iff_forall_eigenvalue]
      intro ν hν
      obtain ⟨x, hx⟩ := hν.exists_hasEigenvector
      have hxne : (x : H) ≠ 0 := fun h0 => hx.2 (Subtype.ext h0)
      have happ := hx.apply_eq_smul

      have hRx : R (x : H) = (ν + 1) • (x : H) := by
        have h2 : ((T x : W) : H) = R x := rfl
        have h3 : (((T - algebraMap k (Module.End k W) 1) x : W) : H) = R x - x := by
          simp [LinearMap.sub_apply, h2]
        have h4 : (((T - algebraMap k (Module.End k W) 1) x : W) : H) = ν • (x : H) := by
          rw [happ]; rfl
        rw [add_smul, one_smul, ← h4, h3, sub_add_cancel]
      have := key (ν + 1) x hxne hRx
      simpa using this
    have hT : T = 1 := by
      have := (sub_eq_zero (a := T)).mp hT1
      rw [this, map_one]
    have := LinearMap.congr_fun hT ⟨a, self_mem_orbit a⟩
    simpa [T, LinearMap.restrict_apply, Subtype.ext_iff] using this

  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  have h := congrArg (Coalgebra.counit (R := k) (A := H)) (hRid a)
  rw [hRψ, counit_rho] at h
  change φ a = (1 : WithConv (H →ₐ[k] k)) a
  rw [AlgHom.convOne_apply]
  simpa using h

end Rho

end P2mAffineTorsionUnip
p2m_reactivate "P2MW.S_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem.P2mAffineTorsionUnip"

open P2mAffineTorsionUnip in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (H : Type v) [CommRing H] [HopfAlgebra k H]
    [Coalgebra.IsCocomm k H]
    (φ : WithConv (H →ₐ[k] k)) (m : ℕ) (hm : (m : k) ≠ 0) (hφ : φ ^ m = 1)
    (h1 : ∀ g : H, IsGroupLikeElem k g → φ g = 1) :
    φ = 1 :=
  P2mAffineTorsionUnip.main φ m hm hφ h1

end S_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
end P2MW
export P2MW.S_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem (solution)
