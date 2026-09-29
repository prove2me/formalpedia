-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_ne_zero_forall_apply_principalSeries2Rep_eq_det_mul_of_ne_top_of_forall_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2b70f4a9-ade1-51b3-bd60-1237c18872c2

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_forall_mem_principalSeries2_invariant_mem_span
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_Module_End_exists_dual_ne_zero_forall_apply_eq_mul_of_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_apply_principalSeries2Rep_eq_det_mul_of_ne_top_of_forall_sub_mem

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace WsF
namespace W5c

section Avg

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℂ M]

def avgL (ρ : G →* Module.End ℂ M) (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)] : Module.End ℂ M :=
  ((Fintype.card (H ⧸ K) : ℂ))⁻¹ • ∑ c : H ⧸ K, ρ ((c.out : H) : G)

theorem avgL_apply (ρ : G →* Module.End ℂ M) (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)] (m : M) :
    avgL ρ H K m = ((Fintype.card (H ⧸ K) : ℂ))⁻¹ • ∑ c : H ⧸ K, ρ ((c.out : H) : G) m := by
  simp [avgL, LinearMap.sum_apply]

theorem sum_translate_eq (ρ : G →* Module.End ℂ M) (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)]
    (m : M) (hm : ∀ k : H, k ∈ K → ρ (k : G) m = m) (h : H) :
    ∑ c : H ⧸ K, ρ ((h : G) * ((c.out : H) : G)) m = ∑ c : H ⧸ K, ρ ((c.out : H) : G) m := by
  classical
  have key : ∀ c : H ⧸ K, ρ ((h : G) * ((c.out : H) : G)) m = ρ ((((h • c : H ⧸ K)).out : H) : G) m := by
    intro c
    have hc : (h • c : H ⧸ K) = QuotientGroup.mk (h * c.out) := by
      conv_lhs => rw [← Quotient.out_eq c]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (h * c.out)
    rw [hc, hk, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hm k k.2, map_mul, Module.End.mul_apply]
  simp_rw [key]
  exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun c => rfl)

theorem apply_avgL (ρ : G →* Module.End ℂ M) (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)]
    (m : M) (hm : ∀ k : H, k ∈ K → ρ (k : G) m = m) (h : H) :
    ρ (h : G) (avgL ρ H K m) = avgL ρ H K m := by
  rw [avgL_apply, map_smul, map_sum]
  congr 1
  simp_rw [← Module.End.mul_apply, ← map_mul]
  exact sum_translate_eq ρ H K m hm h

theorem avgL_eq_self (ρ : G →* Module.End ℂ M) (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)] [Nonempty (H ⧸ K)]
    (m : M) (hm : ∀ h : H, ρ (h : G) m = m) : avgL ρ H K m = m := by
  rw [avgL_apply]
  simp_rw [hm]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

theorem avgL_sub_mem_span (ρ : G →* Module.End ℂ M) (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)]
    [Nonempty (H ⧸ K)] (m : M) :
    avgL ρ H K m - m ∈ Submodule.span ℂ {x : M | ∃ (h : G) (m' : M), h ∈ H ∧ x = ρ h m' - m'} := by
  have hN : ((Fintype.card (H ⧸ K) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : m = ((Fintype.card (H ⧸ K) : ℂ))⁻¹ • ∑ _c : H ⧸ K, m := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have key : avgL ρ H K m - m =
      ((Fintype.card (H ⧸ K) : ℂ))⁻¹ • ∑ c : H ⧸ K, (ρ ((c.out : H) : G) m - m) := by
    rw [Finset.sum_sub_distrib, smul_sub, ← hm, avgL_apply]
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => Submodule.subset_span ?_)
  exact ⟨((c.out : H) : G), m, (c.out : H).2, rfl⟩

theorem avgL_comm (ρ : G →* Module.End ℂ M) (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)]
    (T : Module.End ℂ M) (hT : ∀ h : H, T * ρ (h : G) = ρ (h : G) * T) (m : M) :
    avgL ρ H K (T m) = T (avgL ρ H K m) := by
  rw [avgL_apply, avgL_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Module.End.mul_apply, ← hT, Module.End.mul_apply]

theorem map_avgL {M' : Type*} [AddCommGroup M'] [Module ℂ M'] (ρ : G →* Module.End ℂ M) (ρ' : G →* Module.End ℂ M')
    (π : M →ₗ[ℂ] M') (hπ : ∀ (g : G) (m : M), π (ρ g m) = ρ' g (π m))
    (H : Subgroup G) (K : Subgroup H) [Fintype (H ⧸ K)] (m : M) :
    π (avgL ρ H K m) = avgL ρ' H K (π m) := by
  rw [avgL_apply, avgL_apply, map_smul, map_sum]
  simp_rw [hπ]

end Avg

section Main

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)

variable (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

set_option quotPrecheck false in
local notation "PS" => ↥(principalSeries2 p θ)
local notation "ρ" => principalSeries2Rep θ

theorem rep_apply_coe (g h : G) (f : PS) : ((ρ g f : PS) : G → ℂ) h = (f : G → ℂ) (h * g) := rfl

theorem exists_open_stab (f : PS) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ρ k f = f := by
  obtain ⟨U, hU, hfix⟩ :=
    LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2 p θ (f : G → ℂ) f.2
  refine ⟨U, hU, fun k hk => ?_⟩
  apply Subtype.ext
  funext h
  rw [rep_apply_coe]
  exact hfix k hk h

theorem main (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ PS)
    (hV : ∀ (g : G), ∀ v ∈ V, ρ g v ∈ V)
    (hVtop : V ≠ ⊤)
    (hsl : ∀ (g : G), Matrix.GeneralLinearGroup.det g = 1 → ∀ f : PS, ρ g f - f ∈ V) :
    ∃ (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (lam : PS →ₗ[ℂ] ℂ),
      lam ≠ 0 ∧ (∀ f ∈ V, lam f = 0) ∧
      ∀ (g : G) (f : PS), lam (ρ g f) = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * lam f := by
  classical

  let Q := PS ⧸ V
  let π : PS →ₗ[ℂ] Q := V.mkQ
  let ρQ : G → (Q →ₗ[ℂ] Q) := fun g => V.mapQ V (ρ g) (fun v hv => hV g v hv)
  have hπρ : ∀ (g : G) (f : PS), π (ρ g f) = ρQ g (π f) := fun g f => rfl
  have hρQ_mul : ∀ g h : G, ρQ (g * h) = ρQ g ∘ₗ ρQ h := by
    intro g h
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H f => show π (ρ (g * h) f) = π (ρ g (ρ h f)); rw [map_mul, Module.End.mul_apply]
  have hρQ_one : ρQ 1 = LinearMap.id := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H f => show π (ρ 1 f) = π f; rw [map_one, Module.End.one_apply]

  have hdet : ∀ g h : G, Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h → ρQ g = ρQ h := by
    intro g h hgh
    have h1 : Matrix.GeneralLinearGroup.det (h⁻¹ * g) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
    have : g = h * (h⁻¹ * g) := by group
    rw [this, hρQ_mul]
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H f =>
      show ρQ h (π (ρ (h⁻¹ * g) f)) = ρQ h (π f)
      congr 1
      exact (Submodule.Quotient.eq V).mpr (hsl _ h1 f)

  have hcomm : ∀ g h : G, ρQ g ∘ₗ ρQ h = ρQ h ∘ₗ ρQ g := by
    intro g h
    rw [← hρQ_mul, ← hρQ_mul]
    exact hdet _ _ (by rw [map_mul, map_mul, mul_comm])

  obtain ⟨f₀, hf₀V⟩ : ∃ f₀ : PS, f₀ ∉ V := by
    by_contra hall; push Not at hall
    exact hVtop (eq_top_iff.mpr fun f _ => hall f)
  obtain ⟨Uf₀, hUf₀open, hUf₀⟩ := exists_open_stab θ f₀
  let K2 : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤
  obtain ⟨hK2c, hK2o⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ (by simp)
  let U₀ : Subgroup G := Uf₀ ⊓ K2
  have hU₀open : IsOpen (U₀ : Set G) := hUf₀open.inter hK2o
  have hU₀cpt : IsCompact (U₀ : Set G) := by
    have hcl : IsClosed (U₀ : Set G) := U₀.isClosed_of_isOpen hU₀open
    exact hK2c.of_isClosed_subset hcl (fun x hx => hx.2)
  haveI : CompactSpace U₀ := isCompact_iff_compactSpace.mp hU₀cpt
  have hU₀f₀ : ∀ k ∈ U₀, ρ k f₀ = f₀ := fun k hk => hUf₀ k hk.1

  have finQ : ∀ U' : Subgroup G, IsOpen (U' : Set G) → Finite (U₀ ⧸ (U' ⊓ U₀).subgroupOf U₀) := by
    intro U' hU'
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    have : ((U' ⊓ U₀).subgroupOf U₀ : Set U₀) = Subtype.val ⁻¹' (U' : Set G) := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact hU'.preimage continuous_subtype_val

  let R : Submodule ℂ Q := Submodule.span ℂ {x : Q | ∃ (h : G) (q : Q), h ∈ U₀ ∧ x = ρQ h q - q}
  have hR : ∀ (g : G), ∀ x ∈ R, ρQ g x ∈ R := by
    intro g x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro x ⟨h, q, hh, rfl⟩
      refine Submodule.subset_span ⟨h, ρQ g q, hh, ?_⟩
      rw [map_sub, ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
    · rw [map_zero]; exact R.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact R.add_mem hx hy
    · intro a x _ hx; rw [map_smul]; exact R.smul_mem a hx
  let W := Q ⧸ R
  let πW : Q →ₗ[ℂ] W := R.mkQ
  let τ : G → Module.End ℂ W := fun g => R.mapQ R (ρQ g) (hR g)
  have hπτ : ∀ (g : G) (q : Q), πW (ρQ g q) = τ g (πW q) := fun g q => rfl
  have hτcomm : ∀ g h : G, Commute (τ g) (τ h) := by
    intro g h
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H q =>
      show πW ((ρQ g ∘ₗ ρQ h) q) = πW ((ρQ h ∘ₗ ρQ g) q)
      rw [hcomm]
  have hτdet : ∀ g h : G, Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h → τ g = τ h := by
    intro g h hgh
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H q => show πW (ρQ g q) = πW (ρQ h q); rw [hdet g h hgh]
  have hτmul : ∀ g h : G, τ (g * h) = τ g * τ h := by
    intro g h
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H q => show πW (ρQ (g * h) q) = πW (ρQ g (ρQ h q)); rw [hρQ_mul]; rfl
  have hτone : τ 1 = 1 := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H q => show πW (ρQ 1 q) = πW q; rw [hρQ_one]; rfl

  let ρQh : G →* Module.End ℂ Q :=
    { toFun := ρQ, map_one' := hρQ_one, map_mul' := fun g h => by rw [hρQ_mul]; rfl }
  have hρQh : ∀ g, ρQh g = ρQ g := fun _ => rfl
  let PSinv : Submodule ℂ PS :=
    { carrier := {f | ∀ k ∈ U₀, ρ k f = f}
      zero_mem' := fun k _ => map_zero _
      add_mem' := fun {a b} ha hb k hk => by rw [map_add, ha k hk, hb k hk]
      smul_mem' := fun a {f} hf k hk => by rw [map_smul, hf k hk] }
  have hPSinv_fd : FiniteDimensional ℂ PSinv := by
    obtain ⟨B, hB⟩ :=
      LanglandsTunnell.CubicInduction.exists_finset_forall_mem_principalSeries2_invariant_mem_span p θ c hcθ U₀ hU₀open
    have hle : PSinv.map (principalSeries2 p θ).subtype ≤ Submodule.span ℂ (B : Set (G → ℂ)) := by
      rintro _ ⟨f, hf, rfl⟩
      refine hB (f : G → ℂ) f.2 fun k hk g => ?_
      have := congrArg (fun φ : PS => (φ : G → ℂ) g) (hf k hk)
      simpa [rep_apply_coe] using this
    haveI : FiniteDimensional ℂ ↥(PSinv.map (principalSeries2 p θ).subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) PSinv).symm
  let S : Submodule ℂ Q := PSinv.map π
  haveI : FiniteDimensional ℂ S := by
    haveI := hPSinv_fd; exact Module.Finite.map _ _

  have avg_pack : ∀ U' : Subgroup G, IsOpen (U' : Set G) →
      ∃ (A : Module.End ℂ PS) (Ā : Module.End ℂ Q),
        (∀ f : PS, π (A f) = Ā (π f)) ∧
        (∀ f : PS, (∀ k ∈ U', ρ k f = f) → A f ∈ PSinv) ∧
        (∀ q : Q, (∀ h ∈ U₀, ρQ h q = q) → Ā q = q) ∧
        (∀ q : Q, Ā q - q ∈ R) ∧
        (∀ (h : G) (q : Q), h ∈ U₀ → Ā (ρQ h q) = ρQ h (Ā q)) ∧
        (∀ q : Q, (∀ k ∈ U₀, k ∈ U' → ρQ k q = q) → ∀ h ∈ U₀, ρQ h (Ā q) = Ā q) := by
    intro U' hU'
    haveI : Finite (U₀ ⧸ (U' ⊓ U₀).subgroupOf U₀) := finQ U' hU'
    letI : Fintype (U₀ ⧸ (U' ⊓ U₀).subgroupOf U₀) := Fintype.ofFinite _
    haveI : Nonempty (U₀ ⧸ (U' ⊓ U₀).subgroupOf U₀) := ⟨QuotientGroup.mk 1⟩
    refine ⟨avgL ρ U₀ ((U' ⊓ U₀).subgroupOf U₀), avgL ρQh U₀ ((U' ⊓ U₀).subgroupOf U₀), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun f => map_avgL ρ ρQh π hπρ _ _ f
    · intro f hf k hk
      have hfix : ∀ k' : U₀, k' ∈ (U' ⊓ U₀).subgroupOf U₀ → ρ (k' : G) f = f := fun k' hk' =>
        hf k' (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk')).1
      exact apply_avgL ρ U₀ _ f hfix ⟨k, hk⟩
    · intro q hq
      exact avgL_eq_self ρQh U₀ _ q (fun h => hq h h.2)
    · intro q
      exact avgL_sub_mem_span ρQh U₀ _ q
    · intro h q hh
      refine avgL_comm ρQh U₀ _ (ρQ h) (fun h' => ?_) q
      show ρQ h ∘ₗ ρQ h' = ρQ h' ∘ₗ ρQ h
      exact hcomm _ _
    · intro q hq h hh
      have hfix : ∀ k' : U₀, k' ∈ (U' ⊓ U₀).subgroupOf U₀ → ρQh (k' : G) q = q := fun k' hk' =>
        hq k' k'.2 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk')).1
      exact apply_avgL ρQh U₀ _ q hfix ⟨h, hh⟩

  have hf₀Q : ∀ h ∈ U₀, ρQ h (π f₀) = π f₀ := fun h hh => by rw [← hπρ, hU₀f₀ h hh]
  have hq₀R : π f₀ ∉ R := by
    intro hmem
    obtain ⟨n, a, gen, hsum⟩ := Submodule.mem_span_set'.mp hmem

    have hgen : ∀ i : Fin n, ∃ (h : G) (q : Q), h ∈ U₀ ∧ (gen i : Q) = ρQ h q - q := fun i => (gen i).2
    choose hs qs hhs hgs using hgen
    have hlift : ∀ i : Fin n, ∃ f : PS, π f = qs i := fun i => Submodule.Quotient.mk_surjective V (qs i)
    choose fs hfs using hlift
    have hst : ∀ i : Fin n, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ρ k (fs i) = fs i :=
      fun i => exists_open_stab θ (fs i)
    choose Us hUso hUs using hst
    let U' : Subgroup G := ⨅ i, Us i
    have hU'open : IsOpen (U' : Set G) := by
      rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite fun i => hUso i
    obtain ⟨A, Ā, -, -, hĀfix, -, hĀcomm, hĀinv⟩ := avg_pack U' hU'open

    have hkill : ∀ i : Fin n, Ā (gen i : Q) = 0 := by
      intro i
      have hqfix : ∀ h ∈ U₀, h ∈ U' → ρQ h (qs i) = qs i := by
        intro h _ hh'
        rw [← hfs, ← hπρ, hUs i h (Subgroup.mem_iInf.mp hh' i)]
      have hĀq : Ā (ρQ (hs i) (qs i)) = Ā (qs i) := by
        rw [hĀcomm _ _ (hhs i)]
        exact hĀinv (qs i) (fun k hk hk' => hqfix k hk hk') (hs i) (hhs i)
      rw [hgs, map_sub, hĀq, sub_self]
    have : π f₀ = 0 := by
      rw [← hĀfix _ hf₀Q, ← hsum, map_sum]
      simp only [map_smul, hkill, smul_zero, Finset.sum_const_zero]
    exact hf₀V ((Submodule.Quotient.mk_eq_zero V).mp this)
  haveI : Nontrivial W := by
    refine ⟨⟨πW (π f₀), 0, fun h0 => hq₀R ?_⟩⟩
    exact (Submodule.Quotient.mk_eq_zero R).mp h0

  have hSR : ∀ q : Q, ∃ s ∈ S, q - s ∈ R := by
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective V q
    obtain ⟨Uf, hUfo, hUf⟩ := exists_open_stab θ f
    obtain ⟨A, Ā, hπA, hAinv, -, hĀR, -, -⟩ := avg_pack Uf hUfo
    refine ⟨Ā (π f), ?_, ?_⟩
    · rw [← hπA]; exact Submodule.mem_map_of_mem (hAinv f hUf)
    · have := R.neg_mem (hĀR (π f)); rwa [neg_sub] at this
  haveI : FiniteDimensional ℂ W := by
    refine Module.Finite.of_surjective (πW ∘ₗ S.subtype) fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H q =>
      obtain ⟨s, hs, hqs⟩ := hSR q
      refine ⟨⟨s, hs⟩, ?_⟩
      show πW s = πW q
      exact ((Submodule.Quotient.eq R).mpr (by have := R.neg_mem hqs; rwa [neg_sub] at this))

  obtain ⟨μ, cτ, hμ0, hμ⟩ := Module.End.exists_dual_ne_zero_forall_apply_eq_mul_of_commute τ hτcomm
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, μ w₀ ≠ 0 := by
    by_contra hall; push Not at hall
    exact hμ0 (LinearMap.ext fun w => by simpa using hall w)

  have hc_eq : ∀ g h : G, τ g = τ h → cτ g = cτ h := by
    intro g h hgh
    have := hμ g w₀; rw [hgh, hμ h w₀] at this
    exact (mul_left_injective₀ hw₀ this).symm
  have hc_mul : ∀ g h : G, cτ (g * h) = cτ g * cτ h := by
    intro g h
    have e1 := hμ (g * h) w₀
    rw [hτmul, Module.End.mul_apply, hμ g, hμ h, ← mul_assoc] at e1
    exact (mul_left_injective₀ hw₀ e1).symm
  have hc_one : cτ 1 = 1 := by
    have := hμ 1 w₀; rw [hτone, Module.End.one_apply] at this
    exact mul_left_injective₀ hw₀ (this.symm.trans (one_mul _).symm)
  have hc_ne : ∀ g : G, cτ g ≠ 0 := fun g h0 => by
    have := hc_mul g g⁻¹; rw [mul_inv_cancel, hc_one, h0, zero_mul] at this; exact one_ne_zero this

  let d : (p.adicCompletion ℚ)ˣ → G := fun a =>
    ⟨Matrix.diagonal ![(a : F), 1], Matrix.diagonal ![((a⁻¹ : (p.adicCompletion ℚ)ˣ) : F), 1],
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp⟩
  have hdet_d : ∀ a, Matrix.GeneralLinearGroup.det (d a) = a := fun a => by
    ext; simp [d, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  let χ : (p.adicCompletion ℚ)ˣ →* ℂˣ :=
    { toFun := fun a => Units.mk0 (cτ (d a)) (hc_ne _)
      map_one' := by
        apply Units.ext
        show cτ (d 1) = 1
        rw [hc_eq (d 1) 1 (hτdet _ _ (by rw [hdet_d, map_one])), hc_one]
      map_mul' := fun a b => by
        apply Units.ext
        show cτ (d (a * b)) = cτ (d a) * cτ (d b)
        rw [← hc_mul, hc_eq (d (a * b)) (d a * d b) (hτdet _ _ (by rw [map_mul, hdet_d, hdet_d, hdet_d]))] }
  have hχ : ∀ g : G, ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = cτ g := fun g => by
    show cτ (d (Matrix.GeneralLinearGroup.det g)) = cτ g
    exact hc_eq _ _ (hτdet _ _ (hdet_d _))

  refine ⟨χ, μ ∘ₗ πW ∘ₗ π, ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨q, hq⟩ := Submodule.Quotient.mk_surjective R w₀
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective V q
    apply hw₀
    have := congrArg (fun φ : PS →ₗ[ℂ] ℂ => φ f) h0
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    rw [← hq, ← hf]; exact this
  · intro f hf
    show μ (πW (π f)) = 0
    have hπf : π f = 0 := (Submodule.Quotient.mk_eq_zero V).mpr hf
    rw [hπf, map_zero, map_zero]
  · intro g f
    show μ (πW (π (ρ g f))) = _ * μ (πW (π f))
    rw [hπρ, hπτ, hμ, hχ]

end Main

end WsF.W5c

end

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hVtop : V ≠ ⊤)
    (hsl : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), Matrix.GeneralLinearGroup.det g = 1 →
      ∀ f : ↥(principalSeries2 p θ), principalSeries2Rep θ g f - f ∈ V) :
    ∃ (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (lam : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ),
      lam ≠ 0 ∧ (∀ f ∈ V, lam f = 0) ∧
      ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)) (f : ↥(principalSeries2 p θ)),
        lam (principalSeries2Rep θ g f) = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * lam f :=
  WsF.W5c.main θ c hcθ V hV hVtop hsl

end S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_apply_principalSeries2Rep_eq_det_mul_of_ne_top_of_forall_sub_mem
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_apply_principalSeries2Rep_eq_det_mul_of_ne_top_of_forall_sub_mem (solution)
