-- Prove2me | solution 1 for ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/77925553-0ce8-5ac2-8900-e152776f97d0

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center
import Theorems.Thm_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups

namespace P2mKuroshTor

section Crossed

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {A B : Type*} [AddCommGroup A]
  [AddCommGroup B]

def tr (g : G) (F : Ω → A) : Ω → A := fun x => F (g⁻¹ • x)

omit [AddCommGroup A] in
@[scoped simp] theorem tr_apply (g : G) (F : Ω → A) (x : Ω) : tr g F x = F (g⁻¹ • x) := rfl

omit [AddCommGroup A] in
theorem tr_one (F : Ω → A) : tr (1 : G) F = F := by
  funext x; simp [tr]

omit [AddCommGroup A] in
theorem tr_mul (g h : G) (F : Ω → A) : tr (g * h) F = tr g (tr h F) := by
  funext x; simp [tr, mul_smul, mul_inv_rev]

theorem tr_add (g : G) (F F' : Ω → A) : tr g (F + F') = tr g F + tr g F' := rfl

theorem tr_sub (g : G) (F F' : Ω → A) : tr g (F - F') = tr g F - tr g F' := rfl

theorem tr_neg (g : G) (F : Ω → A) : tr g (-F) = -tr g F := rfl

theorem tr_zero (g : G) : tr g (0 : Ω → A) = 0 := rfl

theorem tr_zsmul (g : G) (n : ℤ) (F : Ω → A) : tr g (n • F) = n • tr g F := rfl

def IsCrossed (c : G → Ω → A) : Prop := ∀ g h : G, c (g * h) = c g + tr g (c h)

namespace IsCrossed

variable {c c' : G → Ω → A}

theorem map_one (hc : IsCrossed c) : c 1 = 0 := by
  have h := hc 1 1
  rw [mul_one, tr_one] at h
  have : c 1 + c 1 = c 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem map_inv (hc : IsCrossed c) (g : G) : c g⁻¹ = -tr g⁻¹ (c g) := by
  have h := hc g⁻¹ g
  rw [inv_mul_cancel, hc.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem map_inv_apply (hc : IsCrossed c) (g : G) (x : Ω) : c g⁻¹ x = -c g (g • x) := by
  rw [hc.map_inv]; simp

theorem conj_apply (hc : IsCrossed c) (g γ : G) (y : Ω) (hy : γ • y = y) :
    c (g * γ * g⁻¹) (g • y) = c γ y := by
  have hy' : γ⁻¹ • y = y := by
    conv_lhs => rw [← hy]
    rw [inv_smul_smul]
  rw [hc, hc, hc.map_inv]
  simp only [Pi.add_apply, tr_apply, Pi.neg_apply, inv_smul_smul, mul_inv_rev, inv_inv, mul_smul,
    hy']
  abel

theorem add (hc : IsCrossed c) (hc' : IsCrossed c') : IsCrossed (c + c') := by
  intro g h
  simp only [Pi.add_apply, hc g h, hc' g h, tr_add]
  abel

theorem neg (hc : IsCrossed c) : IsCrossed (-c) := by
  intro g h
  simp only [Pi.neg_apply, hc g h, tr_neg]
  abel

theorem sub (hc : IsCrossed c) (hc' : IsCrossed c') : IsCrossed (c - c') := by
  rw [sub_eq_add_neg]; exact hc.add hc'.neg

theorem zsmul (hc : IsCrossed c) (n : ℤ) : IsCrossed (n • c) := by
  intro g h
  simp only [Pi.smul_apply, hc g h, smul_add, tr_zsmul]

theorem map (hc : IsCrossed c) (π : A →+ B) : IsCrossed (fun g x => π (c g x)) := by
  intro g h
  funext x
  simp only [hc g h, Pi.add_apply, map_add, tr_apply]

end IsCrossed

def cob (F : Ω → A) : G → Ω → A := fun g => F - tr g F

theorem cob_apply (F : Ω → A) (g : G) (x : Ω) : cob F g x = F x - F (g⁻¹ • x) := rfl

theorem isCrossed_cob (F : Ω → A) : IsCrossed (cob (G := G) F) := by
  intro g h
  simp only [cob, tr_sub, tr_mul]
  abel

theorem cob_apply_of_smul_eq (F : Ω → A) {γ : G} {y : Ω} (hy : γ • y = y) : cob F γ y = 0 := by
  have hy' : γ⁻¹ • y = y := by
    conv_lhs => rw [← hy]
    rw [inv_smul_smul]
  rw [cob_apply, hy', sub_self]

theorem cob_map (F : Ω → A) (π : A →+ B) (g : G) (x : Ω) :
    π (cob F g x) = cob (G := G) (fun y => π (F y)) g x := by
  simp [cob_apply]

theorem exists_potential {c : G → Ω → A} (hc : IsCrossed c) (K : Subgroup G)
    (hK : ∀ k ∈ K, ∀ y : Ω, k • y = y → c k y = 0) :
    ∃ f : Ω → A, ∀ k ∈ K, c k = cob f k := by
  classical

  let base : Ω → Ω := fun x => (Quotient.mk (MulAction.orbitRel K Ω) x).out
  have hbase : ∀ x : Ω, ∃ s : G, s ∈ K ∧ s • base x = x := by
    intro x
    have hrel : (MulAction.orbitRel K Ω) (base x) x := Quotient.mk_out x
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨u, hu⟩ := hrel
    refine ⟨((u⁻¹ : K) : G), (u⁻¹).2, ?_⟩
    rw [← hu, ← Subgroup.smul_def, inv_smul_smul]
  choose s hsK hs using hbase
  have hbase_smul : ∀ k ∈ K, ∀ x : Ω, base (k • x) = base x := by
    intro k hk x
    show (Quotient.mk (MulAction.orbitRel K Ω) (k • x)).out = (Quotient.mk (MulAction.orbitRel K Ω) x).out
    congr 1
    exact Quotient.sound ⟨⟨k, hk⟩, rfl⟩
  refine ⟨fun x => c (s x) x, ?_⟩
  intro k hk
  funext x
  rw [cob_apply]
  have hb : base (k⁻¹ • x) = base x := hbase_smul k⁻¹ (inv_mem hk) x
  have hs' : s (k⁻¹ • x) • base x = k⁻¹ • x := by rw [← hb]; exact hs _
  have hsx : (s x)⁻¹ • x = base x := by rw [inv_smul_eq_iff, hs x]

  have hκK : (s x)⁻¹ * k * s (k⁻¹ • x) ∈ K := mul_mem (mul_mem (inv_mem (hsK x)) hk) (hsK _)
  have hκy : ((s x)⁻¹ * k * s (k⁻¹ • x)) • base x = base x := by
    rw [mul_smul, mul_smul, hs', smul_inv_smul, hsx]
  have hκ0 : c ((s x)⁻¹ * k * s (k⁻¹ • x)) (base x) = 0 := hK _ hκK _ hκy

  have hdecomp : s (k⁻¹ • x) = k⁻¹ * (s x * ((s x)⁻¹ * k * s (k⁻¹ • x))) := by group
  have key : c (s (k⁻¹ • x)) (k⁻¹ • x) = -c k x + c (s x) x := by
    rw [hdecomp, hc, hc]
    simp only [Pi.add_apply, tr_apply, inv_inv]
    rw [hc.map_inv_apply, smul_inv_smul, hsx, hκ0, add_zero]
  rw [key]; abel

def trAut (g : G) : Multiplicative (Ω → A) ≃* Multiplicative (Ω → A) :=
  AddEquiv.toMultiplicative
    { toFun := tr g
      invFun := tr g⁻¹
      left_inv := fun F => by simp [← tr_mul, tr_one (G := G)]
      right_inv := fun F => by simp [← tr_mul, tr_one (G := G)]
      map_add' := tr_add g }

@[scoped simp] theorem trAut_apply (g : G) (F : Multiplicative (Ω → A)) :
    trAut g F = Multiplicative.ofAdd (tr g (Multiplicative.toAdd F)) := rfl

variable (G Ω A) in

def trHom : G →* MulAut (Multiplicative (Ω → A)) where
  toFun := trAut
  map_one' := by
    ext F
    simp [tr_one (G := G)]
  map_mul' g h := by
    ext F
    simp [tr_mul]

theorem trHom_apply (g : G) (F : Multiplicative (Ω → A)) :
    trHom G Ω A g F = Multiplicative.ofAdd (tr g (Multiplicative.toAdd F)) := rfl

end Crossed

section Shapiro

variable {G : Type*} [Group G] (H : Subgroup G) {A B : Type*} [AddCommGroup A] [AddCommGroup B]

abbrev bs : G ⧸ H := ((1 : G) : G ⧸ H)

theorem smul_coe (g a : G) : g • ((a : G) : G ⧸ H) = ((g * a : G) : G ⧸ H) := rfl

theorem smul_bs (g : G) : g • bs H = (g : G ⧸ H) := by
  rw [bs, smul_coe, mul_one]

theorem smul_bs_eq_bs_iff (g : G) : g • bs H = bs H ↔ g ∈ H := by
  rw [smul_bs, bs, eq_comm, QuotientGroup.eq, inv_one, one_mul]

theorem smul_bs_of_mem {g : G} (hg : g ∈ H) : g • bs H = bs H := (smul_bs_eq_bs_iff H g).mpr hg

variable {H}

theorem char_congr (ψ : Additive H →+ B) {P Q : G} (hP : P ∈ H) (hQ : Q ∈ H) (h : P = Q) :
    ψ (Additive.ofMul ⟨P, hP⟩) = ψ (Additive.ofMul ⟨Q, hQ⟩) := by
  subst h; rfl

theorem char_mul (ψ : Additive H →+ B) {P Q : G} (hP : P ∈ H) (hQ : Q ∈ H) :
    ψ (Additive.ofMul ⟨P * Q, mul_mem hP hQ⟩)
      = ψ (Additive.ofMul ⟨P, hP⟩) + ψ (Additive.ofMul ⟨Q, hQ⟩) := by
  rw [← map_add]; rfl

theorem char_inv (ψ : Additive H →+ B) {P : G} (hP : P ∈ H) :
    ψ (Additive.ofMul ⟨P⁻¹, inv_mem hP⟩) = -ψ (Additive.ofMul ⟨P, hP⟩) := by
  rw [← map_neg]; rfl

theorem char_conj (ψ : Additive H →+ B) {h P : G} (hh : h ∈ H) (hP : P ∈ H) :
    ψ (Additive.ofMul ⟨h⁻¹ * P * h, mul_mem (mul_mem (inv_mem hh) hP) hh⟩)
      = ψ (Additive.ofMul ⟨P, hP⟩) := by
  rw [char_mul ψ (mul_mem (inv_mem hh) hP) hh, char_mul ψ (inv_mem hh) hP, char_inv ψ hh]
  abel

variable (H)

def evalBase (c : G → (G ⧸ H) → A) (hc : IsCrossed c) : Additive H →+ A where
  toFun γ := c ((Additive.toMul γ : H) : G) (bs H)
  map_zero' := by
    show c ((1 : H) : G) (bs H) = 0
    rw [OneMemClass.coe_one, hc.map_one]; rfl
  map_add' γ δ := by
    show c ((Additive.toMul γ * Additive.toMul δ : H) : G) (bs H)
      = c ((Additive.toMul γ : H) : G) (bs H) + c ((Additive.toMul δ : H) : G) (bs H)
    rw [Subgroup.coe_mul, hc, Pi.add_apply, tr_apply,
      smul_bs_of_mem H (inv_mem (Additive.toMul γ).2)]

@[scoped simp] theorem evalBase_apply (c : G → (G ⧸ H) → A) (hc : IsCrossed c) (P : G) (hP : P ∈ H) :
    evalBase H c hc (Additive.ofMul ⟨P, hP⟩) = c P (bs H) := rfl

theorem evalBase_map (c : G → (G ⧸ H) → A) (hc : IsCrossed c) (π : A →+ B) :
    π.comp (evalBase H c hc) = evalBase H (fun g x => π (c g x)) (hc.map π) := by
  ext γ; rfl

theorem evalBase_sub (c c' : G → (G ⧸ H) → A) (hc : IsCrossed c) (hc' : IsCrossed c') :
    evalBase H (c - c') (hc.sub hc') = evalBase H c hc - evalBase H c' hc' := by
  ext γ; rfl

theorem evalBase_zsmul (c : G → (G ⧸ H) → A) (hc : IsCrossed c) (n : ℤ) :
    evalBase H (n • c) (hc.zsmul n) = n • evalBase H c hc := by
  ext γ; rfl

theorem evalBase_conj (c : G → (G ⧸ H) → A) (hc : IsCrossed c) (g γ : G)
    (hγ : γ • (g⁻¹ • bs H) = g⁻¹ • bs H) (hmem : g * γ * g⁻¹ ∈ H) :
    evalBase H c hc (Additive.ofMul ⟨g * γ * g⁻¹, hmem⟩) = c γ (g⁻¹ • bs H) := by
  rw [evalBase_apply, ← hc.conj_apply g γ (g⁻¹ • bs H) hγ, smul_inv_smul]

theorem conj_mem_iff_smul (g γ : G) : g * γ * g⁻¹ ∈ H ↔ γ • (g⁻¹ • bs H) = g⁻¹ • bs H := by
  rw [← smul_bs_eq_bs_iff, mul_smul, mul_smul, smul_eq_iff_eq_inv_smul]

theorem out_inv_mul_mul_out_mem (g : G) (x : G ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_coe, QuotientGroup.out_eq',
    smul_inv_smul]

noncomputable def shapiro (ψ : Additive H →+ B) : G → (G ⧸ H) → B :=
  fun g x => ψ (Additive.ofMul ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, out_inv_mul_mul_out_mem H g x⟩)

theorem shapiro_apply (ψ : Additive H →+ B) (g : G) (x : G ⧸ H) :
    shapiro H ψ g x
      = ψ (Additive.ofMul ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, out_inv_mul_mul_out_mem H g x⟩) := rfl

theorem isCrossed_shapiro (ψ : Additive H →+ B) : IsCrossed (shapiro H ψ) := by
  intro g h
  funext x
  rw [Pi.add_apply, tr_apply, shapiro_apply, shapiro_apply, shapiro_apply,
    ← char_mul ψ (out_inv_mul_mul_out_mem H g x) (out_inv_mul_mul_out_mem H h (g⁻¹ • x))]
  apply char_congr
  have hx : (g * h)⁻¹ • x = h⁻¹ • g⁻¹ • x := by rw [mul_inv_rev, mul_smul]
  rw [hx]
  group

theorem evalBase_shapiro (ψ : Additive H →+ B) :
    evalBase H (shapiro H ψ) (isCrossed_shapiro H ψ) = ψ := by
  refine AddMonoidHom.ext (Additive.ofMul.surjective.forall.mpr ?_)
  rintro ⟨P, hP⟩
  rw [evalBase_apply, shapiro_apply]
  have h0 : ((bs H).out : G) ∈ H := by
    rw [← smul_bs_eq_bs_iff, smul_bs, QuotientGroup.out_eq']
  have hfix : P⁻¹ • bs H = bs H := smul_bs_of_mem H (inv_mem hP)
  rw [← char_conj ψ h0 hP]
  apply char_congr
  rw [hfix]

end Shapiro

section FreeProduct

variable {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
variable {Ω : Type*} [MulAction (Monoid.CoprodI M) Ω] {A B : Type*} [AddCommGroup A] [AddCommGroup B]

open Monoid.CoprodI

theorem IsCrossed.ext_of {c c' : Monoid.CoprodI M → Ω → A} (hc : IsCrossed c) (hc' : IsCrossed c')
    (h : ∀ (i : ι) (m : M i), c (of m) = c' (of m)) : c = c' := by
  funext g
  induction g using Monoid.CoprodI.induction_on with
  | one => rw [hc.map_one, hc'.map_one]
  | of i m => exact h i m
  | mul x y hx hy => rw [hc, hc', hx, hy]

def genHom (F : ι → Ω → A) (i : ι) :
    M i →* (Multiplicative (Ω → A)) ⋊[trHom (Monoid.CoprodI M) Ω A] Monoid.CoprodI M where
  toFun m := ⟨Multiplicative.ofAdd (cob (F i) (of m)), of m⟩
  map_one' := by
    apply SemidirectProduct.ext
    · simp only [map_one, SemidirectProduct.one_left]
      rw [(isCrossed_cob (F i)).map_one]; rfl
    · simp
  map_mul' m m' := by
    apply SemidirectProduct.ext
    · simp only [map_mul, SemidirectProduct.mul_left]
      rw [(isCrossed_cob (F i))]
      show _ = Multiplicative.ofAdd (cob (F i) (of m))
        * trHom (Monoid.CoprodI M) Ω A (of m) (Multiplicative.ofAdd _)
      rw [trHom_apply, toAdd_ofAdd]
      rfl
    · simp

def totalHom (F : ι → Ω → A) :
    Monoid.CoprodI M →* (Multiplicative (Ω → A)) ⋊[trHom (Monoid.CoprodI M) Ω A] Monoid.CoprodI M :=
  Monoid.CoprodI.lift (genHom F)

theorem totalHom_right (F : ι → Ω → A) (g : Monoid.CoprodI M) : (totalHom F g).right = g := by
  have h : (SemidirectProduct.rightHom.comp (totalHom (M := M) (A := A) F)) = MonoidHom.id _ := by
    apply Monoid.CoprodI.ext_hom
    intro i
    ext m
    simp [totalHom, genHom, SemidirectProduct.rightHom]
  exact DFunLike.congr_fun h g

def liftCrossed (F : ι → Ω → A) : Monoid.CoprodI M → Ω → A :=
  fun g => Multiplicative.toAdd (totalHom F g).left

theorem isCrossed_liftCrossed (F : ι → Ω → A) : IsCrossed (liftCrossed (M := M) F) := by
  intro g h
  simp only [liftCrossed, map_mul, SemidirectProduct.mul_left, totalHom_right, trHom_apply]
  rfl

theorem liftCrossed_of (F : ι → Ω → A) (i : ι) (m : M i) :
    liftCrossed (M := M) F (of m) = cob (F i) (of m) := by
  simp only [liftCrossed, totalHom, Monoid.CoprodI.lift_of, genHom, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd]

end FreeProduct

section Main

variable {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

open Monoid.CoprodI

theorem exists_char_comp_eq_of_forall_conj_of (H : Subgroup (Monoid.CoprodI M)) (π : A →+ B)
    (hπ : Function.Surjective π) (ψ : Additive H →+ B)
    (hψ : ∀ (i : ι) (x : M i) (g : Monoid.CoprodI M) (h : g * of x * g⁻¹ ∈ H),
      ψ (Additive.ofMul ⟨g * of x * g⁻¹, h⟩) = 0) :
    ∃ χ : Additive H →+ A, π.comp χ = ψ ∧
      ∀ (i : ι) (x : M i) (g : Monoid.CoprodI M) (h : g * of x * g⁻¹ ∈ H),
        χ (Additive.ofMul ⟨g * of x * g⁻¹, h⟩) = 0 := by
  classical

  set c₀ := shapiro H ψ with hc₀def
  have hc₀ : IsCrossed c₀ := isCrossed_shapiro H ψ

  have hkill : ∀ (i : ι), ∀ k ∈ (of : M i →* Monoid.CoprodI M).range, ∀ y : Monoid.CoprodI M ⧸ H,
      k • y = y → c₀ k y = 0 := by
    rintro i k ⟨x, rfl⟩ y hy

    have hyr : y = (y.out : Monoid.CoprodI M) • bs H := by rw [smul_bs, QuotientGroup.out_eq']
    set r : Monoid.CoprodI M := y.out
    have hfix : (r⁻¹ * of x * r⁻¹⁻¹) • bs H = bs H := by
      rw [inv_inv, mul_smul, mul_smul, ← hyr, hy, hyr, inv_smul_smul]
    have hmem : r⁻¹ * of x * r⁻¹⁻¹ ∈ H := (smul_bs_eq_bs_iff H _).mp hfix
    have h1 : c₀ (of x) y = c₀ (r * (r⁻¹ * of x * r⁻¹⁻¹) * r⁻¹) (r • bs H) := by
      rw [← hyr]; congr 1; group
    rw [h1, hc₀.conj_apply r _ (bs H) hfix]
    have h2 := hψ i x r⁻¹ hmem
    rwa [← evalBase_shapiro (H := H) ψ, evalBase_apply] at h2

  have hpot : ∀ i : ι, ∃ f : (Monoid.CoprodI M ⧸ H) → B, ∀ x : M i, c₀ (of x) = cob f (of x) := by
    intro i
    obtain ⟨f, hf⟩ := exists_potential hc₀ (of : M i →* Monoid.CoprodI M).range (hkill i)
    exact ⟨f, fun x => hf (of x) ⟨x, rfl⟩⟩
  choose f hf using hpot
  let F : ι → (Monoid.CoprodI M ⧸ H) → A := fun i y => Function.surjInv hπ (f i y)
  have hF : ∀ i y, π (F i y) = f i y := fun i y => Function.surjInv_eq hπ (f i y)

  set C := liftCrossed (M := M) (Ω := Monoid.CoprodI M ⧸ H) F with hCdef
  have hC : IsCrossed C := isCrossed_liftCrossed F
  have hπC : (fun g y => π (C g y)) = c₀ := by
    apply (hC.map π).ext_of hc₀
    intro i m
    funext y
    rw [hCdef, liftCrossed_of, cob_map, hf i m]
    simp only [hF]
  refine ⟨evalBase H C hC, ?_, ?_⟩
  · rw [evalBase_map]
    have hev : ∀ (a b : Monoid.CoprodI M → (Monoid.CoprodI M ⧸ H) → B) (ha : IsCrossed a)
        (hb : IsCrossed b), a = b → evalBase H a ha = evalBase H b hb := by
      rintro a b ha hb rfl; rfl
    rw [hev _ c₀ (hC.map π) hc₀ hπC]
    exact evalBase_shapiro H ψ
  · intro i x g h
    have hfix : of x • g⁻¹ • bs H = g⁻¹ • bs H := (conj_mem_iff_smul (H := H) g (of x)).mp h
    rw [evalBase_conj H C hC g (of x) hfix h, hCdef, liftCrossed_of]
    exact cob_apply_of_smul_eq (F i) hfix

end Main

section CuspGeneral

variable {G : Type*} [Group G] (H : Subgroup G) {B : Type*} [AddCommGroup B]

theorem char_zpow (ψ : Additive H →+ B) {P : G} (hP : P ∈ H) (m : ℤ) :
    ψ (Additive.ofMul ⟨P ^ m, zpow_mem hP m⟩) = m • ψ (Additive.ofMul ⟨P, hP⟩) := by
  rw [← map_zsmul, ← ofMul_zpow]; rfl

theorem char_conj_zpow_eq_zero [H.FiniteIndex] (t : G) (ψ : Additive H →+ B)
    (hψ : ∀ q : Quotient (MulAction.orbitRel (Subgroup.zpowers t) (G ⧸ H)),
      ψ (Additive.ofMul ⟨q.out.out⁻¹ * t ^ Function.minimalPeriod (t • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H t q.out⟩) = 0)
    (g : G) (k : ℤ) (h : g * t ^ k * g⁻¹ ∈ H) : ψ (Additive.ofMul ⟨g * t ^ k * g⁻¹, h⟩) = 0 := by
  classical
  haveI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex

  set e₀ : G ⧸ H := ((g⁻¹ : G) : G ⧸ H) with he₀
  have hfix : t ^ k • e₀ = e₀ := by
    rw [he₀]
    show (((t ^ k * g⁻¹ : G)) : G ⧸ H) = ((g⁻¹ : G) : G ⧸ H)
    rw [QuotientGroup.eq]
    have : (t ^ k * g⁻¹)⁻¹ * g⁻¹ = (g * t ^ k * g⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem h

  set w : ℕ := Function.minimalPeriod (t • ·) e₀ with hw
  obtain ⟨m, hm⟩ : (w : ℤ) ∣ k := MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mp hfix

  set q : Quotient (MulAction.orbitRel (Subgroup.zpowers t) (G ⧸ H)) :=
    Quotient.mk (MulAction.orbitRel (Subgroup.zpowers t) (G ⧸ H)) e₀ with hq
  set a : G := q.out.out with ha
  have haq : (a : G ⧸ H) = q.out := QuotientGroup.out_eq' _

  have hrel : q.out ∈ MulAction.orbit (Subgroup.zpowers t) e₀ := by
    have := Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers t) (G ⧸ H)) e₀
    rwa [MulAction.orbitRel_apply] at this
  obtain ⟨⟨u, hu⟩, hue⟩ := MulAction.mem_orbit_iff.mp hrel
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hj : t ^ j • e₀ = q.out := hue

  have horb : MulAction.orbit (Subgroup.zpowers t) q.out = MulAction.orbit (Subgroup.zpowers t) e₀ :=
    MulAction.orbit_eq_iff.mpr hrel
  have hw' : Function.minimalPeriod (t • ·) q.out = w := by
    rw [hw, MulAction.minimalPeriod_eq_card, MulAction.minimalPeriod_eq_card, Fintype.card_eq_nat_card,
      Fintype.card_eq_nat_card]
    exact congrArg (fun s : Set (G ⧸ H) => Nat.card s) horb

  have h₁ : g * t ^ (-j) * a ∈ H := by
    have h2 : (((t ^ j * g⁻¹ : G)) : G ⧸ H) = (a : G ⧸ H) := by
      rw [haq, ← hj, he₀]; rfl
    rw [QuotientGroup.eq] at h2
    have : (t ^ j * g⁻¹)⁻¹ * a = g * t ^ (-j) * a := by group
    rwa [this] at h2
  have hp : a⁻¹ * t ^ w * a ∈ H := by
    have := QuotientGroup.out_conj_pow_minimalPeriod_mem H t q.out
    rwa [hw'] at this
  have hp0 : ψ (Additive.ofMul ⟨a⁻¹ * t ^ w * a, hp⟩) = 0 := by
    have := hψ q

    have hgen : q.out.out⁻¹ * t ^ Function.minimalPeriod (t • ·) q.out * q.out.out = a⁻¹ * t ^ w * a := by
      rw [hw']
    rwa [char_congr ψ _ hp hgen] at this

  have hdec : g * t ^ k * g⁻¹ = (g * t ^ (-j) * a) * (a⁻¹ * t ^ w * a) ^ m * (g * t ^ (-j) * a)⁻¹ := by
    have e1 : (a⁻¹ * t ^ w * a) ^ m = a⁻¹ * (t ^ w) ^ m * a := by
      have := (conj_zpow (a := a⁻¹) (b := t ^ w) (i := m))
      rwa [inv_inv] at this
    rw [e1, ← zpow_natCast, ← zpow_mul, ← hm]
    group
  rw [char_congr ψ h (mul_mem (mul_mem h₁ (zpow_mem hp m)) (inv_mem h₁)) hdec,
    char_mul ψ (mul_mem h₁ (zpow_mem hp m)) (inv_mem h₁), char_mul ψ h₁ (zpow_mem hp m),
    char_inv ψ h₁, char_zpow H ψ hp m, hp0, smul_zero]
  abel

theorem sum_char_cuspGen_eq_zero [H.FiniteIndex] {t₁ t₂ : G} (h₁ : IsOfFinOrder t₁) (h₂ : IsOfFinOrder t₂)
    (χ : Additive H →+ ℤ) [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers (t₁ * t₂)) (G ⧸ H)))] :
    ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers (t₁ * t₂)) (G ⧸ H)),
      χ (Additive.ofMul ⟨q.out.out⁻¹ * (t₁ * t₂) ^ Function.minimalPeriod ((t₁ * t₂) • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H (t₁ * t₂) q.out⟩) = 0 := by
  set f : H →* Multiplicative ℤ := AddMonoidHom.toMultiplicativeRight χ with hf
  have hfin : ∀ {s : G}, IsOfFinOrder s → f.transfer s = 1 := by
    intro s hs
    have := f.transfer.isOfFinOrder hs
    exact (isOfFinAddOrder_iff_eq_zero (G := ℤ) _).mp this
  have htr := f.transfer_eq_prod_quotient_orbitRel_zpowers_quot (t₁ * t₂)
  rw [map_mul, hfin h₁, hfin h₂, mul_one] at htr
  have := congrArg Multiplicative.toAdd htr
  rw [toAdd_one, toAdd_prod] at this
  rw [← this.symm]
  rfl

end CuspGeneral

section Cusp

abbrev M23 : Fin 2 → Type := fun i => Multiplicative (ZMod (i.val + 2))

abbrev G23 : Type := Monoid.CoprodI M23

def tP : G23 := Monoid.CoprodI.of (M := M23) (i := 0) (Multiplicative.ofAdd 1) *
  Monoid.CoprodI.of (M := M23) (i := 1) (Multiplicative.ofAdd 1)

theorem isOfFinOrder_of_M23 {i : Fin 2} (x : M23 i) : IsOfFinOrder (Monoid.CoprodI.of (M := M23) x) :=
  (Monoid.CoprodI.of).isOfFinOrder (isOfFinOrder_of_finite x)

variable (H : Subgroup G23) [H.FiniteIndex]

theorem exists_sub_smul_apply_conj_zpow_eq_zero (χ : Additive H →+ ℤ) (n : ℕ)
    (hdvd : ∀ (g : G23) (k : ℤ) (h : g * tP ^ k * g⁻¹ ∈ H), (n : ℤ) ∣ χ (Additive.ofMul ⟨_, h⟩)) :
    ∃ φ' : Additive H →+ ℤ, ∀ (g : G23) (k : ℤ) (h : g * tP ^ k * g⁻¹ ∈ H),
      (χ - (n : ℤ) • φ') (Additive.ofMul ⟨_, h⟩) = 0 := by
  classical
  haveI : Fintype (G23 ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  let Q := Quotient (MulAction.orbitRel (Subgroup.zpowers tP) (G23 ⧸ H))
  let p : Q → G23 := fun q => q.out.out⁻¹ * tP ^ Function.minimalPeriod (tP • ·) q.out * q.out.out
  have hp : ∀ q, p q ∈ H := fun q => QuotientGroup.out_conj_pow_minimalPeriod_mem H tP q.out
  let a : Q → ℤ := fun q => χ (Additive.ofMul ⟨p q, hp q⟩) / n
  have hdvd' : ∀ q, (n : ℤ) ∣ χ (Additive.ofMul ⟨p q, hp q⟩) := by
    intro q
    have hmem : q.out.out⁻¹ * tP ^ ((Function.minimalPeriod (tP • ·) q.out : ℕ) : ℤ) * q.out.out⁻¹⁻¹ ∈ H := by
      rw [zpow_natCast, inv_inv]; exact hp q
    have := hdvd (q.out.out⁻¹) (Function.minimalPeriod (tP • ·) q.out : ℕ) hmem
    rwa [char_congr χ hmem (hp q) (by rw [zpow_natCast, inv_inv])] at this
  have ha1 : ∀ q, (n : ℤ) * a q = χ (Additive.ofMul ⟨p q, hp q⟩) := fun q => Int.mul_ediv_cancel' (hdvd' q)
  have hsum : ∑ q : Q, χ (Additive.ofMul ⟨p q, hp q⟩) = 0 :=
    sum_char_cuspGen_eq_zero H (isOfFinOrder_of_M23 _) (isOfFinOrder_of_M23 _) χ
  have ha0 : ∑ᶠ q, a q = 0 := by
    rw [finsum_eq_sum_of_fintype]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a]
    · have h1 : (n : ℤ) * ∑ q, a q = 0 := by
        rw [Finset.mul_sum]
        simp_rw [ha1]
        exact hsum
      exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hn)
  obtain ⟨φ', hφ'⟩ :=
    Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero tP rfl H ℤ a ha0
  refine ⟨φ', ?_⟩
  have hgen : ∀ q : Q, (χ - (n : ℤ) • φ') (Additive.ofMul ⟨p q, hp q⟩) = 0 := by
    intro q
    have hp' : q.out.out⁻¹ * tP ^ Function.minimalPeriod (tP • ·) ((q.out.out : G23) : G23 ⧸ H) * q.out.out
        ∈ H := by
      rw [QuotientGroup.out_eq']; exact hp q
    have h1 := hφ' q.out.out hp'
    have h2 : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers tP) (G23 ⧸ H)) (q.out.out : G23 ⧸ H) = q := by
      rw [QuotientGroup.out_eq', Quotient.out_eq]
    rw [h2, char_congr φ' hp' (hp q) (by rw [QuotientGroup.out_eq'])] at h1
    rw [AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply, smul_eq_mul]
    change χ (Additive.ofMul ⟨p q, hp q⟩) - (n : ℤ) * φ' (Additive.ofMul ⟨p q, hp q⟩) = 0
    rw [h1, ha1, sub_self]
  exact char_conj_zpow_eq_zero H tP _ hgen

end Cusp

section SL2

open Matrix.SpecialLinearGroup ModularGroup

theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) :=
  Subgroup.mem_center_iff.mpr fun g => by rw [mul_neg_one, neg_one_mul]

theorem eq_one_or_eq_neg_one_of_mem_center {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2, ℤ)) :
    z = 1 ∨ z = -1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  rcases sq_eq_one_iff.mp hr2 with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hrz, map_one, Matrix.SpecialLinearGroup.coe_one]
  · right
    apply Subtype.ext
    rw [← hrz, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

theorem S_mul_S : (S : SL(2, ℤ)) * S = -1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S_mul_S_eq, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])

theorem trace_conj_T_zpow (δ : SL(2, ℤ)) (k : ℤ) :
    ((δ * T ^ k * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
  ring

private theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  exact h

private theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  show ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem inv_entries (A : SL(2, ℤ)) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  have h : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

theorem exists_col_eq {p r : ℤ} (h : IsCoprime p r) :
    ∃ δ : SL(2, ℤ), δ 0 0 = p ∧ δ 1 0 = r := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨!![p, -v; r, u], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination huv

theorem eq_T_zpow_of_col {M : SL(2, ℤ)} (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) :
    M = T ^ (M 0 1) := by
  have hdet := det_entries M
  rw [h00, h10, one_mul, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [ModularGroup.coe_T_zpow]

theorem exists_isCoprime_fixed {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) (hc : γ 1 0 ≠ 0) :
    ∃ p r : ℤ, IsCoprime p r ∧
      γ 0 0 * p + γ 0 1 * r = p ∧ γ 1 0 * p + γ 1 1 * r = r := by
  rw [Matrix.trace_fin_two] at htr
  have hdet := det_entries γ
  have hgcd_pos : 0 < Int.gcd (γ 0 0 - 1) (γ 1 0) := by
    rcases Nat.eq_zero_or_pos (Int.gcd (γ 0 0 - 1) (γ 1 0)) with h | h
    · exact absurd (Int.gcd_eq_zero_iff.mp h).2 hc
    · exact h
  obtain ⟨p, r, hpr, hp, hr⟩ := Int.exists_gcd_one hgcd_pos
  set g : ℤ := (Int.gcd (γ 0 0 - 1) (γ 1 0) : ℤ) with hgdef
  have hgne : g ≠ 0 := by
    rw [hgdef]
    exact_mod_cast hgcd_pos.ne'
  refine ⟨p, r, Int.isCoprime_iff_gcd_eq_one.mpr hpr, ?_, ?_⟩
  · have key : g * (γ 0 0 * p + γ 0 1 * r - p) = 0 := by
      linear_combination (-(γ 0 0 - 1)) * hp - γ 0 1 * hr + γ 0 0 * htr - hdet
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith
  · have key : g * (γ 1 0 * p + γ 1 1 * r - r) = 0 := by
      linear_combination (-(γ 1 0)) * hp - (γ 1 1 - 1) * hr + γ 1 0 * htr
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith

theorem exists_conj_T_zpow_of_trace_eq_two {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) :
    ∃ (δ : SL(2, ℤ)) (n : ℤ), γ = δ * T ^ n * δ⁻¹ := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hdet := det_entries γ
    rw [hc, mul_zero, sub_zero] at hdet
    rw [Matrix.trace_fin_two] at htr
    have hsq : (γ 0 0 - 1) ^ 2 = 0 := by
      linear_combination γ 0 0 * htr - hdet
    have ha : γ 0 0 = 1 := by
      have := sq_eq_zero_iff.mp hsq
      linarith
    refine ⟨1, γ 0 1, ?_⟩
    rw [inv_one, mul_one, one_mul]
    exact eq_T_zpow_of_col ha hc
  · obtain ⟨p, r, hpr, hfix1, hfix2⟩ := exists_isCoprime_fixed htr hc
    obtain ⟨δ, hδ00, hδ10⟩ := exists_col_eq hpr
    obtain ⟨hi00, hi01, hi10, hi11⟩ := inv_entries δ
    have hδdet := det_entries δ
    rw [hδ00, hδ10] at hδdet
    have hγδ0 : (γ * δ) 0 0 = δ 0 0 := by
      rw [mul_entry γ δ 0 0, hδ00, hδ10]; exact hfix1
    have hγδ1 : (γ * δ) 1 0 = δ 1 0 := by
      rw [mul_entry γ δ 1 0, hδ00, hδ10]; exact hfix2
    have hM00 : (δ⁻¹ * (γ * δ)) 0 0 = 1 := by
      rw [mul_entry δ⁻¹ (γ * δ) 0 0, hγδ0, hγδ1, hi00, hi01, hδ00, hδ10]
      linear_combination hδdet
    have hM10 : (δ⁻¹ * (γ * δ)) 1 0 = 0 := by
      rw [mul_entry δ⁻¹ (γ * δ) 1 0, hγδ0, hγδ1, hi10, hi11, hδ00, hδ10]
      ring
    refine ⟨δ, (δ⁻¹ * (γ * δ)) 0 1, ?_⟩
    rw [← eq_T_zpow_of_col hM00 hM10]
    group

theorem exists_eq_or_neg_eq_conj_T_zpow {γ : SL(2, ℤ)}
    (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    ∃ (δ : SL(2, ℤ)) (n : ℤ), γ = δ * T ^ n * δ⁻¹ ∨ -γ = δ * T ^ n * δ⁻¹ := by
  have hsplit : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace - 2) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace + 2) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hsplit with h2 | h2
  · obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two (γ := γ) (by linarith)
    exact ⟨δ, n, Or.inl hδ⟩
  · have htrneg : ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]
      linarith
    obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two htrneg
    exact ⟨δ, n, Or.inr hδ⟩

end SL2

section Bridge

open Matrix.SpecialLinearGroup ModularGroup

variable (ρ : SL(2, ℤ) →* G23) (hker : ∀ z, ρ z = 1 ↔ z ∈ Subgroup.center SL(2, ℤ))
  (hT : ρ T = tP)

include hker

theorem rho_neg (γ : SL(2, ℤ)) : ρ (-γ) = ρ γ := by
  rw [← neg_one_mul, map_mul, (hker _).mpr neg_one_mem_center, one_mul]

theorem eq_or_eq_neg_of_rho_eq {γ δ : SL(2, ℤ)} (h : ρ γ = ρ δ) : γ = δ ∨ γ = -δ := by
  have h1 : ρ (δ⁻¹ * γ) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases eq_one_or_eq_neg_one_of_mem_center ((hker _).mp h1) with h2 | h2
  · left; exact (inv_mul_eq_one.mp h2).symm
  · right
    rw [inv_mul_eq_iff_eq_mul] at h2
    rw [h2, mul_neg_one]

theorem isOfFinOrder_of_rho {γ : SL(2, ℤ)} (h : IsOfFinOrder (ρ γ)) : IsOfFinOrder γ := by
  obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq_one
  rw [← map_pow] at hpow
  rcases eq_one_or_eq_neg_one_of_mem_center ((hker _).mp hpow) with h2 | h2
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, h2⟩
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n * 2, by omega, ?_⟩
    rw [pow_mul, h2, sq, neg_mul_neg, one_mul]

theorem isOfFinOrder_of_rho_eq_conj_of {γ : SL(2, ℤ)} {i : Fin 2} (x : M23 i) (g : G23)
    (h : ρ γ = g * Monoid.CoprodI.of (M := M23) x * g⁻¹) : IsOfFinOrder γ := by
  apply isOfFinOrder_of_rho ρ hker
  obtain ⟨n, hn, hxn⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  rw [h, conj_pow, ← map_pow, hxn, map_one, mul_one, mul_inv_cancel]

include hT

theorem exists_rho_eq_conj_tP_zpow {γ : SL(2, ℤ)} (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    ∃ (g : G23) (k : ℤ), ρ γ = g * tP ^ k * g⁻¹ := by
  obtain ⟨δ, k, hδ⟩ := exists_eq_or_neg_eq_conj_T_zpow h
  refine ⟨ρ δ, k, ?_⟩
  rcases hδ with hδ | hδ
  · rw [hδ, map_mul, map_mul, map_zpow, map_inv, hT]
  · rw [← rho_neg ρ hker γ, hδ, map_mul, map_mul, map_zpow, map_inv, hT]

omit hker in
include hker in

theorem trace_sq_of_rho_eq_conj_tP_zpow (hsurj : Function.Surjective ρ) {γ : SL(2, ℤ)} {g : G23} {k : ℤ}
    (h : ρ γ = g * tP ^ k * g⁻¹) : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  obtain ⟨δ, rfl⟩ := hsurj g
  have h' : ρ γ = ρ (δ * T ^ k * δ⁻¹) := by
    rw [h, map_mul, map_mul, map_zpow, map_inv, hT]
  rcases eq_or_eq_neg_of_rho_eq ρ hker h' with h2 | h2
  · rw [h2, trace_conj_T_zpow]; norm_num
  · have : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = -2 := by
      rw [h2, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, trace_conj_T_zpow]
    rw [this]; norm_num

end Bridge

section MainProof

open Matrix.SpecialLinearGroup ModularGroup

theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : ModularCurve.Period.parabolicHoms (ZMod n) Γ (ZMod n))
    (hφ : ∀ γ : Γ, IsOfFinOrder γ → (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) = 0) :
    ∃ x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
      (Int.castAddHom (ZMod n)).comp (x : Additive Γ →+ ℤ) = (φ : Additive Γ →+ ZMod n) := by
  classical
  obtain ⟨e, he0, he1⟩ := ModularGroup.exists_mulEquiv_freeProduct_quotient_center

  let ρ : SL(2, ℤ) →* G23 := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
  have hρ : ∀ z, ρ z = e.symm (QuotientGroup.mk z) := fun z => rfl
  have hker : ∀ z, ρ z = 1 ↔ z ∈ Subgroup.center SL(2, ℤ) := by
    intro z
    rw [hρ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective ρ :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hT : ρ T = tP := by
    rw [hρ, MulEquiv.symm_apply_eq, tP, map_mul, he0, he1, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      ← mul_assoc S, S_mul_S, neg_one_mul, mul_neg, inv_mul_cancel]
    exact neg_one_mem_center

  let H : Subgroup G23 := Γ.map ρ
  haveI : H.FiniteIndex := ⟨fun h0 =>
    Subgroup.FiniteIndex.index_ne_zero (H := Γ) (Nat.eq_zero_of_zero_dvd (h0 ▸ Γ.index_map_dvd hsurj))⟩
  let ρΓ : Γ →* H := ρ.subgroupMap Γ
  have hρΓ : ∀ γ : Γ, ((ρΓ γ : H) : G23) = ρ γ := fun γ => rfl
  let ρΓa : Additive Γ →+ Additive H := MonoidHom.toAdditive ρΓ
  have hρΓa : ∀ γ : Γ, ρΓa (Additive.ofMul γ) = Additive.ofMul (ρΓ γ) := fun γ => rfl
  have hρΓa_surj : Function.Surjective ρΓa := ρ.subgroupMap_surjective Γ

  have hkerle : ρΓa.ker ≤ (φ : Additive Γ →+ ZMod n).ker := by
    refine Additive.ofMul.surjective.forall.mpr ?_
    intro γ hγ
    rw [AddMonoidHom.mem_ker] at hγ ⊢
    apply hφ γ
    have h1 : ρ γ = 1 := by
      rw [← hρΓ]
      have : ρΓ γ = 1 := hγ
      rw [this]; rfl
    have h2 : IsOfFinOrder (γ : SL(2, ℤ)) :=
      isOfFinOrder_of_rho ρ hker (by rw [h1]; exact IsOfFinOrder.one)
    exact Submonoid.isOfFinOrder_coe.mp h2
  let ψ : Additive H →+ ZMod n := ρΓa.liftOfSurjective hρΓa_surj ⟨(φ : Additive Γ →+ ZMod n), hkerle⟩
  have hψ : ∀ γ : Γ, ψ (Additive.ofMul (ρΓ γ)) = (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) := by
    intro γ
    rw [← hρΓa]
    exact AddMonoidHom.liftOfRightInverse_comp_apply ρΓa _ _ ⟨(φ : Additive Γ →+ ZMod n), hkerle⟩
      (Additive.ofMul γ)
  have hψ' : ∀ (P : G23) (hP : P ∈ H), ∃ γ : Γ, ρ γ = P ∧
      ψ (Additive.ofMul ⟨P, hP⟩) = (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) := by
    intro P hP
    obtain ⟨γ, hγ, hγP⟩ := Subgroup.mem_map.mp hP
    refine ⟨⟨γ, hγ⟩, hγP, ?_⟩
    have : (⟨P, hP⟩ : H) = ρΓ ⟨γ, hγ⟩ := Subtype.ext hγP.symm
    rw [this]
    exact hψ ⟨γ, hγ⟩

  have hψfac : ∀ (i : Fin 2) (x : M23 i) (g : G23) (h : g * Monoid.CoprodI.of x * g⁻¹ ∈ H),
      ψ (Additive.ofMul ⟨g * Monoid.CoprodI.of x * g⁻¹, h⟩) = 0 := by
    intro i x g h
    obtain ⟨γ, hγ, hval⟩ := hψ' _ h
    rw [hval]
    apply hφ γ
    exact Submonoid.isOfFinOrder_coe.mp (isOfFinOrder_of_rho_eq_conj_of ρ hker x g hγ)

  have hψpar : ∀ (g : G23) (k : ℤ) (h : g * tP ^ k * g⁻¹ ∈ H),
      ψ (Additive.ofMul ⟨g * tP ^ k * g⁻¹, h⟩) = 0 := by
    intro g k h
    obtain ⟨γ, hγ, hval⟩ := hψ' _ h
    rw [hval]
    exact φ.2 γ (trace_sq_of_rho_eq_conj_tP_zpow ρ hker hT hsurj hγ)

  obtain ⟨χ, hχ, -⟩ := exists_char_comp_eq_of_forall_conj_of H (Int.castAddHom (ZMod n))
    ZMod.intCast_surjective ψ hψfac

  have hdvd : ∀ (g : G23) (k : ℤ) (h : g * tP ^ k * g⁻¹ ∈ H),
      (n : ℤ) ∣ χ (Additive.ofMul ⟨_, h⟩) := by
    intro g k h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    have := DFunLike.congr_fun hχ (Additive.ofMul ⟨_, h⟩)
    rw [AddMonoidHom.comp_apply, hψpar g k h] at this
    exact this

  obtain ⟨φ', hφ'⟩ := exists_sub_smul_apply_conj_zpow_eq_zero H χ n hdvd

  let x : Additive Γ →+ ℤ := (χ - (n : ℤ) • φ').comp ρΓa
  have hxpar : ModularCurve.Period.IsParabolicHom Γ x := by
    intro γ hγ
    obtain ⟨g, k, hgk⟩ := exists_rho_eq_conj_tP_zpow ρ hker hT hγ
    show (χ - (n : ℤ) • φ') (ρΓa (Additive.ofMul γ)) = 0
    have hmem : g * tP ^ k * g⁻¹ ∈ H := by rw [← hgk]; exact (ρΓ γ).2
    rw [hρΓa]
    have : ρΓ γ = ⟨g * tP ^ k * g⁻¹, hmem⟩ := Subtype.ext hgk
    rw [this]
    exact hφ' g k hmem
  refine ⟨⟨x, hxpar⟩, ?_⟩
  refine AddMonoidHom.ext (Additive.ofMul.surjective.forall.mpr ?_)
  intro γ
  show (Int.castAddHom (ZMod n)) ((χ - (n : ℤ) • φ') (ρΓa (Additive.ofMul γ)))
    = (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ)
  rw [← hψ γ, hρΓa, AddMonoidHom.sub_apply, map_sub, AddMonoidHom.zsmul_apply, map_zsmul]
  have h1 : (Int.castAddHom (ZMod n)) (χ (Additive.ofMul (ρΓ γ))) = ψ (Additive.ofMul (ρΓ γ)) :=
    DFunLike.congr_fun hχ _
  rw [h1, sub_eq_self, natCast_zsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end MainProof

end P2mKuroshTor
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.P2mKuroshTor"

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : ModularCurve.Period.parabolicHoms (ZMod n) Γ (ZMod n))
    (hφ : ∀ γ : Γ, IsOfFinOrder γ → (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) = 0) :
    ∃ x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
      (Int.castAddHom (ZMod n)).comp (x : Additive Γ →+ ℤ) = (φ : Additive Γ →+ ZMod n) :=
  P2mKuroshTor.main Γ n φ hφ

end S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
end P2MW
export P2MW.S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder (solution)
